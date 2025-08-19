open Ast

(* 寄存器分类 *)
type reg_type =
  | CallerSaved   (* 调用者保存寄存器 *)
  | CalleeSaved   (* 被调用者保存寄存器 *)
  | TempReg       (* 临时寄存器 *)

(* 上下文类型 *)
type context = {
    current_func: string;
    local_offset: int; (* Current offset for new local variables, relative to saved_area_size. This is the "next available slot" for locals. *)
    frame_size: int;   (* Final calculated frame size for the current function *)
    var_offset: (string * int) list list; (* Maps variable name to its offset from SP *)
    next_temp: int;
    label_counter: int;
    loop_stack: (string * string * string) list;  (* (begin_label, next_label, end_label) *)
    saved_regs: string list; (* List of callee-saved registers (s0-s11) *)
    reg_map: (string * reg_type) list; (* Map of all available registers and their types *)
    param_count: int; (* Not directly used for stack frame, but good to have *)
    used_regs: string list;  (* Tracks currently used registers (including spilled ones) *)
    saved_area_size: int; (* Size of area for RA and S-registers, at the bottom of the frame (lowest addresses) *)
    max_local_var_offset: int; (* Max offset used by explicit local vars, relative to saved_area_size. This is the highest offset for non-spill locals. *)
    max_concurrent_spills: int; (* Max number of registers simultaneously spilled to stack *)
}

(* 创建新上下文 *)
let create_context func_name =
    let reg_map = [
        ("a0", CallerSaved); ("a1", CallerSaved); ("a2", CallerSaved); ("a3", CallerSaved);
        ("a4", CallerSaved); ("a5", CallerSaved); ("a6", CallerSaved); ("a7", CallerSaved);
        ("s0", CalleeSaved); ("s1", CalleeSaved); ("s2", CalleeSaved); ("s3", CalleeSaved);
        ("s4", CalleeSaved); ("s5", CalleeSaved); ("s6", CalleeSaved); ("s7", CalleeSaved);
        ("s8", CalleeSaved); ("s9", CalleeSaved); ("s10", CalleeSaved); ("s11", CalleeSaved);
        ("t0", TempReg); ("t1", TempReg); ("t2", TempReg); ("t3", TempReg);
        ("t4", TempReg); ("t5", TempReg); ("t6", TempReg)
    ] in
    { current_func = func_name;
      local_offset = 0; (* Starts after saved_area_size *)
      frame_size = 0;   (* Will be calculated later *)
      var_offset = [[]];
      next_temp = 0;
      label_counter = 0;
      loop_stack = [];
      saved_regs = ["s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11"];
      reg_map = reg_map;
      param_count = 0;
      used_regs = [];
      saved_area_size = 52; (* 12 s-regs * 4 bytes + 1 ra * 4 bytes = 52 bytes *)
      max_local_var_offset = 0; (* Max offset relative to sp + saved_area_size *)
      max_concurrent_spills = 0; (* Max number of active spill slots *)
    }

(* 栈对齐常量 *)
let stack_align = 16

(* 获取唯一标签 - 使用函数名作为前缀 *)
let fresh_label ctx prefix =
    let n = ctx.label_counter in
    { ctx with label_counter = n + 1 },
    Printf.sprintf ".L%s_%s%d" ctx.current_func prefix n

(* 获取变量偏移量 - 支持嵌套作用域查找 *)
let get_var_offset ctx name =
    let rec search = function
        | [] -> None
        | scope :: rest ->
            try Some (List.assoc name scope)
            with Not_found -> search rest
    in
    match search ctx.var_offset with
    | Some offset -> offset
    | None -> failwith (Printf.sprintf "Undefined variable: %s" name)

(* 添加变量到当前作用域 *)
let add_var ctx name size =
  match ctx.var_offset with
  | current_scope :: rest_scopes ->
      let offset = ctx.saved_area_size + ctx.local_offset in (* Offset from SP *)
      let new_scope = (name, offset) :: current_scope in
      { ctx with
          var_offset = new_scope :: rest_scopes;
          local_offset = ctx.local_offset + size;
          max_local_var_offset = max ctx.max_local_var_offset (ctx.local_offset + size) (* Update max_local_var_offset *)
      }
  | [] -> failwith "No active scope"

(* 改进的寄存器分配函数 *)
let alloc_temp_reg ctx =
    let temp_regs = ["t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6"] in
    let saved_regs_list = ["s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11"] in
    let all_regs = temp_regs @ saved_regs_list in

    (* Find the first unused physical register *)
    let available_physical_reg = List.find_opt (fun reg ->
        not (List.mem reg ctx.used_regs)) all_regs in

    match available_physical_reg with
    | Some reg ->
        { ctx with used_regs = reg :: ctx.used_regs }, reg
    | None ->
        (* All physical registers are in use, spill to stack *)
        let current_active_spills = List.length (List.filter is_spill_reg ctx.used_regs) in
        let spill_offset = ctx.saved_area_size + ctx.max_local_var_offset + current_active_spills * 4 in
        let spill_reg_name = Printf.sprintf "SPILL_%d" spill_offset in
        { ctx with
            used_regs = spill_reg_name :: ctx.used_regs;
            max_concurrent_spills = max ctx.max_concurrent_spills (current_active_spills + 1);
        }, spill_reg_name

(* 改进的寄存器释放函数 *)
let free_temp_reg ctx reg =
    { ctx with used_regs = List.filter (fun r -> r <> reg) ctx.used_regs }

(* 计算栈对齐 *)
let align_stack size align =
    let remainder = size mod align in
    if remainder = 0 then size else size + (align - remainder)

(* 函数结语生成 *)
let gen_epilogue ctx =
    let restore_regs_asm =
        let ra_offset = (List.length ctx.saved_regs) * 4 in (* ra is saved after all s-regs *)
        let ra_restore = Printf.sprintf "    lw ra, %d(sp)" ra_offset in
        let s_regs_restore =
            List.rev ctx.saved_regs (* Restore in reverse order of saving, s11 first, then s10...s0 *)
            |> List.mapi (fun i reg ->
                let offset = i * 4 in (* s0 at 0, s1 at 4, ..., s11 at 44 *)
                Printf.sprintf "    lw %s, %d(sp)" reg offset)
            |> String.concat "\n" in
        s_regs_restore ^ "\n" ^ ra_restore (* Restore s-regs first, then ra *)
    in

    Printf.sprintf "
%s
    addi sp, sp, %d
    ret
" restore_regs_asm ctx.frame_size

(* 检查是否是溢出寄存器 *)
let is_spill_reg reg =
    String.length reg > 5 && String.sub reg 0 5 = "SPILL"

(* 获取溢出寄存器的栈偏移量 *)
let get_spill_offset reg =
    if is_spill_reg reg then
        int_of_string (String.sub reg 6 (String.length reg - 6))
    else
        failwith (Printf.sprintf "Not a spill register: %s" reg)

(* 生成加载溢出寄存器的代码 *)
let gen_load_spill reg temp_reg =
    if is_spill_reg reg then
        let offset = get_spill_offset reg in
        Printf.sprintf "    lw %s, %d(sp)" temp_reg offset
    else ""

(* 生成存储到溢出寄存器的代码 *)
let gen_store_spill reg temp_reg =
    if is_spill_reg reg then
        let offset = get_spill_offset reg in
        Printf.sprintf "    sw %s, %d(sp)" temp_reg offset
    else ""

(* 表达式代码生成 *)
let rec gen_expr ctx expr =
    match expr with
    | IntLit n ->
        let (ctx, reg) = alloc_temp_reg ctx in
        if is_spill_reg reg then
            let temp_asm = Printf.sprintf "    li t0, %d\n%s" n (gen_store_spill reg "t0") in
            (ctx, temp_asm, reg)
        else
            (ctx, Printf.sprintf "    li %s, %d" reg n, reg)
    | Var name ->
        let offset = get_var_offset ctx name in
        let (ctx, reg) = alloc_temp_reg ctx in
        if is_spill_reg reg then
            let temp_asm = Printf.sprintf "    lw t0, %d(sp)\n%s" offset (gen_store_spill reg "t0") in
            (ctx, temp_asm, reg)
        else
            (ctx, Printf.sprintf "    lw %s, %d(sp)" reg offset, reg)
    | BinOp (e1, op, e2) ->
        let (ctx, asm1, reg1) = gen_expr ctx e1 in
        let (ctx, asm2, reg2) = gen_expr ctx e2 in

        (* If two registers are the same, need to move one to a new register to avoid clobbering *)
        let (ctx, reg2_actual, extra_move_asm) =
            if reg1 = reg2 then
                let (ctx', new_reg) = alloc_temp_reg ctx in
                let load_reg1 = gen_load_spill reg1 "t0" in
                let actual_reg1_val = if is_spill_reg reg1 then "t0" else reg1 in
                let store_new_reg = gen_store_spill new_reg actual_reg1_val in
                (ctx', new_reg, Printf.sprintf "%s\n%s" load_reg1 store_new_reg)
            else
                (ctx, reg2, "")
        in

        (* Handle spill registers *)
        let load1 = gen_load_spill reg1 "t0" in
        let load2 = gen_load_spill reg2_actual "t1" in
        let actual_reg1 = if is_spill_reg reg1 then "t0" else reg1 in
        let actual_reg2 = if is_spill_reg reg2_actual then "t1" else reg2_actual in

        (* Reuse the first register as the destination register *)
        let reg_dest = reg1 in
        let actual_reg_dest = actual_reg1 in

        let instr = match op with
            | Add -> Printf.sprintf "    add %s, %s, %s" actual_reg_dest actual_reg1 actual_reg2
            | Sub -> Printf.sprintf "    sub %s, %s, %s" actual_reg_dest actual_reg1 actual_reg2
            | Mul -> Printf.sprintf "    mul %s, %s, %s" actual_reg_dest actual_reg1 actual_reg2
            | Div -> Printf.sprintf "    div %s, %s, %s" actual_reg_dest actual_reg1 actual_reg2
            | Mod -> Printf.sprintf "    rem %s, %s, %s" actual_reg_dest actual_reg1 actual_reg2
            | Lt  -> Printf.sprintf "    slt %s, %s, %s" actual_reg_dest actual_reg1 actual_reg2
            | Le  -> Printf.sprintf "    slt %s, %s, %s\n    xori %s, %s, 1" actual_reg_dest actual_reg2 actual_reg1 actual_reg_dest actual_reg_dest
            | Gt  -> Printf.sprintf "    slt %s, %s, %s" actual_reg_dest actual_reg2 actual_reg1
            | Ge  -> Printf.sprintf "    slt %s, %s, %s\n    xori %s, %s, 1" actual_reg_dest actual_reg1 actual_reg2 actual_reg_dest actual_reg_dest
            | Eq  -> Printf.sprintf "    sub %s, %s, %s\n    seqz %s, %s" actual_reg_dest actual_reg1 actual_reg2 actual_reg_dest actual_reg_dest
            | Ne  -> Printf.sprintf "    sub %s, %s, %s\n    snez %s, %s" actual_reg_dest actual_reg1 actual_reg2 actual_reg_dest actual_reg_dest
            | And -> Printf.sprintf "    and %s, %s, %s" actual_reg_dest actual_reg1 actual_reg2
            | Or  -> Printf.sprintf "    or %s, %s, %s" actual_reg_dest actual_reg1 actual_reg2
        in

        let store_result = gen_store_spill reg_dest actual_reg_dest in

        let full_asm =
        let parts = [asm1; asm2] @
                 (if extra_move_asm = "" then [] else [extra_move_asm]) @
                 (if load1 = "" then [] else [load1]) @
                 (if load2 = "" then [] else [load2]) @
                 [instr] @
                 (if store_result = "" then [] else [store_result]) in
        String.concat "\n" (List.filter (fun s -> s <> "") parts) in

        (* Free the second register *)
        let ctx = free_temp_reg ctx reg2_actual in
        (ctx, full_asm, reg_dest)

    | UnOp (op, e) ->
        let (ctx, asm, reg) = gen_expr ctx e in
        let load_asm = gen_load_spill reg "t0" in
        let actual_reg = if is_spill_reg reg then "t0" else reg in
        let instr = match op with
        | UPlus  -> Printf.sprintf "    mv %s, %s" actual_reg actual_reg
        | UMinus -> Printf.sprintf "    neg %s, %s" actual_reg actual_reg
        | Not    -> Printf.sprintf "    seqz %s, %s" actual_reg actual_reg
        in
        let store_asm = gen_store_spill reg actual_reg in
        let full_asm =
          let parts = [asm] @
                     (if load_asm = "" then [] else [load_asm]) @
                     [instr] @
                     (if store_asm = "" then [] else [store_asm]) in
          String.concat "\n" (List.filter (fun s -> s <> "") parts) in
        (ctx, full_asm, reg)

    | FuncCall (name, args) ->
    let (ctx, arg_asm, arg_regs) = gen_args ctx args in

    (* Calculate space needed for saving t-registers and for stack arguments *)
    let num_t_regs_to_save = 7 in (* t0-t6 *)
    let t_regs_save_size = num_t_regs_to_save * 4 in
    let num_stack_args = max 0 (List.length args - 8) in
    let stack_args_size = num_stack_args * 4 in
    let temp_space_for_call = t_regs_save_size + stack_args_size in
    let aligned_temp_space = align_stack temp_space_for_call stack_align in

    let stack_adj_asm =
      if aligned_temp_space > 0 then
        Printf.sprintf "    addi sp, sp, -%d" aligned_temp_space
      else "" in

    (* Save t0-t6 to the temporary space on stack *)
    let save_temps_asm =
      List.init num_t_regs_to_save (fun i ->
        Printf.sprintf "    sw t%d, %d(sp)" i (i * 4))
      |> String.concat "\n" in

    let move_args_asm =
      let rec move_args regs index parts =
        match regs with
        | [] -> String.concat "\n" (List.filter (fun s -> s <> "") parts)
        | reg::rest when index < 8 ->
            let target = Printf.sprintf "a%d" index in
            let load_src = gen_load_spill reg "t0" in
            let actual_src = if is_spill_reg reg then "t0" else reg in
            let move_instr =
              if actual_src = target then ""
              else Printf.sprintf "    mv %s, %s" target actual_src
            in
            let new_parts = parts @
              (if load_src = "" then [] else [load_src]) @
              (if move_instr = "" then [] else [move_instr]) in
            move_args rest (index+1) new_parts
        | reg::rest ->
            (* Stack arguments are placed after saved t-registers *)
            let stack_offset = t_regs_save_size + (index - 8) * 4 in
            let load_src = gen_load_spill reg "t0" in
            let actual_src = if is_spill_reg reg then "t0" else reg in
            let store_instr = Printf.sprintf "    sw %s, %d(sp)" actual_src stack_offset in
            let new_parts = parts @
              (if load_src = "" then [] else [load_src]) @
              [store_instr] in
            move_args rest (index+1) new_parts
      in
      move_args arg_regs 0 []
    in

    let call_asm = Printf.sprintf "    call %s\n" name in

    (* Restore t0-t6 from the temporary space on stack *)
    let restore_temps_asm =
      List.init num_t_regs_to_save (fun i ->
        Printf.sprintf "    lw t%d, %d(sp)" i (i * 4))
      |> String.concat "\n" in

    let restore_stack_asm =
      if aligned_temp_space > 0 then
        Printf.sprintf "    addi sp, sp, %d" aligned_temp_space
      else "" in

    (* Allocate result register for a0 *)
    let (ctx, reg_dest) = alloc_temp_reg ctx in

    let move_result =
      if is_spill_reg reg_dest then
        Printf.sprintf "    mv t0, a0\n%s" (gen_store_spill reg_dest "t0")
      else
        Printf.sprintf "    mv %s, a0" reg_dest
    in

    let asm =
      let parts = [arg_asm] @
                 (if stack_adj_asm = "" then [] else [stack_adj_asm]) @
                 (if save_temps_asm = "" then [] else [save_temps_asm]) @
                 (if move_args_asm = "" then [] else [move_args_asm]) @
                 [call_asm] @
                 (if restore_temps_asm = "" then [] else [restore_temps_asm]) @
                 (if restore_stack_asm = "" then [] else [restore_stack_asm]) @
                 [move_result] in
      String.concat "\n" (List.filter (fun s -> s <> "") parts) in

    (* Free parameter registers *)
    let ctx = List.fold_left (fun ctx reg -> free_temp_reg ctx reg) ctx arg_regs in

    (ctx, asm, reg_dest)

(* 生成参数代码 *)
and gen_args ctx args =
  let rec process_args ctx asm regs count = function
    | [] -> (ctx, asm, List.rev regs)
    | arg::rest ->
        let (ctx, arg_asm, reg) = gen_expr ctx arg in
        let new_asm = if asm = "" then arg_asm
                     else asm ^ "\n" ^ arg_asm in
        process_args ctx new_asm (reg::regs) (count+1) rest
  in
  process_args ctx "" [] 0 args

(* 处理语句列表的辅助函数 *)
let rec gen_stmts ctx stmts =
    List.fold_left (fun (ctx, asm) stmt ->
        let (ctx', stmt_asm) = gen_stmt ctx stmt in
        let new_asm = if asm = "" then stmt_asm
                     else if stmt_asm = "" then asm
                     else asm ^ "\n" ^ stmt_asm in
        (ctx', new_asm)
    ) (ctx, "") stmts

(* 语句代码生成 *)
and gen_stmt ctx stmt =
    match stmt with
    | Block stmts ->
        let new_ctx = { ctx with var_offset = [] :: ctx.var_offset } in
        let (ctx_after, asm) = gen_stmts new_ctx stmts in
        let popped_ctx =
            match ctx_after.var_offset with
            | _ :: outer_scopes ->
                { ctx_after with
                    var_offset = outer_scopes;
                    local_offset = ctx.local_offset (* Revert local_offset to parent scope's value *)
                }
            | [] -> failwith "Scope stack underflow"
        in
        (popped_ctx, asm)

    | VarDecl (name, expr) ->
        let (ctx, expr_asm, reg) = gen_expr ctx expr in
        let ctx = add_var ctx name 4 in (* Add var after expr to ensure max_local_var_offset is correct *)
        let offset = get_var_offset ctx name in
        let load_asm = gen_load_spill reg "t0" in
        let actual_reg = if is_spill_reg reg then "t0" else reg in
        let store_instr = Printf.sprintf "    sw %s, %d(sp)" actual_reg offset in
        let asm =
          let parts = [expr_asm] @
                     (if load_asm = "" then [] else [load_asm]) @
                     [store_instr] in
          String.concat "\n" (List.filter (fun s -> s <> "") parts) in
        (free_temp_reg ctx reg, asm)

    | VarAssign (name, expr) ->
        let offset = get_var_offset ctx name in
        let (ctx, expr_asm, reg) = gen_expr ctx expr in
        let load_asm = gen_load_spill reg "t0" in
        let actual_reg = if is_spill_reg reg then "t0" else reg in
        let store_instr = Printf.sprintf "    sw %s, %d(sp)" actual_reg offset in
        let asm =
          let parts = [expr_asm] @
                     (if load_asm = "" then [] else [load_asm]) @
                     [store_instr] in
          String.concat "\n" (List.filter (fun s -> s <> "") parts) in
        (free_temp_reg ctx reg, asm)

     | If (cond, then_stmt, else_stmt) ->
        let (ctx, cond_asm, cond_reg) = gen_expr ctx cond in
        let (ctx, then_label) = fresh_label ctx "if_then" in
        let (ctx, else_label) = fresh_label ctx "if_else" in
        let (ctx, end_label) = fresh_label ctx "if_end" in

        let load_cond = gen_load_spill cond_reg "t0" in
        let actual_cond_reg = if is_spill_reg cond_reg then "t0" else cond_reg in

        let (ctx_then, then_asm) = gen_stmt ctx then_stmt in
        let (ctx_else, else_asm) = match else_stmt with
            | Some s -> gen_stmt ctx s
            | None -> (ctx, "") in

        (* Merge contexts for max stack usage. Other fields should revert to before branch. *)
        let merged_ctx = { ctx with
            max_local_var_offset = max ctx_then.max_local_var_offset ctx_else.max_local_var_offset;
            max_concurrent_spills = max ctx_then.max_concurrent_spills ctx_else.max_concurrent_spills;
        } in

        let asm =
          let parts = [cond_asm] @
                     (if load_cond = "" then [] else [load_cond]) @
                     [Printf.sprintf "    beqz %s, %s" actual_cond_reg else_label] @
                     [Printf.sprintf "    j %s" then_label] @
                     [Printf.sprintf "%s:" else_label] @
                     (if else_asm = "" then [] else [else_asm]) @
                     [Printf.sprintf "    j %s" end_label] @
                     [Printf.sprintf "%s:" then_label] @
                     (if then_asm = "" then [] else [then_asm]) @
                     [Printf.sprintf "    j %s" end_label] @
                     [Printf.sprintf "%s:" end_label] in
          String.concat "\n" (List.filter (fun s -> s <> "") parts) in
        (free_temp_reg merged_ctx cond_reg, asm)

    | While (cond, body) ->
        let (ctx, begin_label) = fresh_label ctx "loop_begin" in
        let (ctx, next_label) = fresh_label ctx "loop_next" in
        let (ctx, end_label) = fresh_label ctx "loop_end" in

        let (ctx_cond, cond_asm, cond_reg) = gen_expr ctx cond in

        let load_cond = gen_load_spill cond_reg "t0" in
        let actual_cond_reg = if is_spill_reg cond_reg then "t0" else cond_reg in

        let loop_ctx = { ctx_cond with
            loop_stack = (begin_label, next_label, end_label) :: ctx_cond.loop_stack } in
        let (ctx_after_body, body_asm) = gen_stmt loop_ctx body in

        (* Merge contexts for max stack usage. Loop body can affect overall max. *)
        let merged_ctx = { ctx_cond with
            max_local_var_offset = max ctx_cond.max_local_var_offset ctx_after_body.max_local_var_offset;
            max_concurrent_spills = max ctx_cond.max_concurrent_spills ctx_after_body.max_concurrent_spills;
            loop_stack = List.tl ctx_after_body.loop_stack (* Pop loop context *)
        } in

        let asm =
          let parts = [Printf.sprintf "%s:" begin_label] @
                     [cond_asm] @
                     (if load_cond = "" then [] else [load_cond]) @
                     [Printf.sprintf "    beqz %s, %s" actual_cond_reg end_label] @
                     (if body_asm = "" then [] else [body_asm]) @
                     [Printf.sprintf "%s:" next_label] @
                     [Printf.sprintf "    j %s" begin_label] @
                     [Printf.sprintf "%s:" end_label] in
          String.concat "\n" (List.filter (fun s -> s <> "") parts) in
        (free_temp_reg merged_ctx cond_reg, asm)

    | Break ->
        (match ctx.loop_stack with
        | (_, _, end_label)::_ ->
            (ctx, Printf.sprintf "    j %s" end_label)
        | [] -> failwith "break outside loop")

    | Continue ->
        (match ctx.loop_stack with
        | (_, next_label, _)::_ ->
            (ctx, Printf.sprintf "    j %s" next_label)
        | [] -> failwith "continue outside loop")

    | Return expr_opt ->
        let (ctx_after_expr, expr_asm, reg) =
            match expr_opt with
            | Some expr ->
                let (ctx_e, asm_e, r_e) = gen_expr ctx expr in
                let load_asm = gen_load_spill r_e "t0" in
                let actual_reg = if is_spill_reg r_e then "t0" else r_e in
                let parts = [asm_e] @
                           (if load_asm = "" then [] else [load_asm]) in
                let full_asm = String.concat "\n" (List.filter (fun s -> s <> "") parts) in
                if actual_reg = "a0" then (ctx_e, full_asm, "a0")
                else (ctx_e, full_asm ^ "\n" ^ Printf.sprintf "    mv a0, %s" actual_reg, "a0")
            | None -> (ctx, "", "a0")
        in
        let epilogue_asm = gen_epilogue ctx_after_expr in (* Use ctx_after_expr for epilogue *)
        (free_temp_reg ctx_after_expr reg, expr_asm ^ "\n" ^ epilogue_asm)
    | EmptyStmt -> (ctx, "")
    | ExprStmt e ->
        let (ctx, asm, reg) = gen_expr ctx e in
        (free_temp_reg ctx reg, asm)

(* 函数代码生成 *)
let gen_function func =
    let ctx_initial = create_context func.name in

    (* 1. Add parameters to the context. This updates max_local_var_offset. *)
    let ctx_after_params =
        List.fold_left (fun ctx param ->
            add_var ctx param 4
        ) ctx_initial func.params
    in

    (* 2. Generate the function body. This will update max_local_var_offset and max_concurrent_spills
          in the returned context as it processes variable declarations and spills. *)
    let (ctx_after_body_gen, body_asm) =
        match func.body with
        | Block stmts -> gen_stmts ctx_after_params stmts
        | _ -> gen_stmt ctx_after_params func.body
    in

    (* 3. Calculate the total frame size based on the maximums observed during body generation. *)
    let total_local_and_spill_space =
        ctx_after_body_gen.max_local_var_offset +
        (ctx_after_body_gen.max_concurrent_spills * 4)
    in

    let actual_frame_size = align_stack
        (ctx_after_body_gen.saved_area_size + total_local_and_spill_space)
        stack_align
    in

    (* 4. Create the final context with the determined frame size. *)
    let final_ctx = { ctx_after_body_gen with frame_size = actual_frame_size } in

    (* 5. Generate the prologue using the calculated frame size. *)
    let prologue_asm =
        let save_regs_asm =
            let ra_offset = (List.length final_ctx.saved_regs) * 4 in
            let reg_saves = List.mapi (fun i reg ->
                Printf.sprintf "    sw %s, %d(sp)" reg (i * 4))
                final_ctx.saved_regs
            in
            let ra_save = Printf.sprintf "    sw ra, %d(sp)" ra_offset in
            String.concat "\n" (reg_saves @ [ra_save])
        in
        Printf.sprintf ".globl %s\n%s:\n    addi sp, sp, -%d\n%s"
            func.name func.name actual_frame_size save_regs_asm
    in

    (* 6. Generate code to save parameters passed in registers to their stack locations. *)
    let save_params_asm =
        let rec gen_save params index asm =
            match params with
            | [] -> asm
            | param::rest ->
                let offset = get_var_offset final_ctx param in
                if index < 8 then (
                    let reg = Printf.sprintf "a%d" index in
                    gen_save rest (index + 1)
                        (asm ^ Printf.sprintf "    sw %s, %d(sp)\n" reg offset)
                ) else (
                    (* Parameters 9 and beyond are on the *caller's* stack frame.
                       Their offset from the *callee's* current sp is:
                       (callee's frame size) + (offset of argument in caller's stack frame)
                       The 9th argument (index 8) is at 0(caller_sp) relative to caller's stack args.
                       When callee enters, its sp moves down by `actual_frame_size`.
                       So, caller's sp is now `callee_sp + actual_frame_size`.
                       Thus, the 9th arg is at `callee_sp + actual_frame_size + 0`.
                       The 10th arg is at `callee_sp + actual_frame_size + 4`.
                    *)
                    let stack_offset_from_callee_sp = final_ctx.frame_size + (index - 8) * 4 in
                    let load_asm = Printf.sprintf "    lw t0, %d(sp)" stack_offset_from_callee_sp in
                    let store_asm = Printf.sprintf "    sw t0, %d(sp)" offset in
                    gen_save rest (index + 1)
                        (asm ^ load_asm ^ "\n" ^ store_asm ^ "\n")
                )
        in
        gen_save func.params 0 ""
    in

    (* 7. Generate the epilogue using the final context. *)
    let epilogue_asm = gen_epilogue final_ctx in

    prologue_asm ^ "\n" ^ save_params_asm ^ body_asm ^ epilogue_asm

(* 编译单元代码生成 *)
let compile cu =
    let main_exists = ref false in
    let funcs_asm = List.map (fun func ->
        if func.name = "main" then main_exists := true;
        gen_function func
    ) cu in

    if not !main_exists then
        failwith "Missing main function";

    String.concat "\n\n" funcs_asm