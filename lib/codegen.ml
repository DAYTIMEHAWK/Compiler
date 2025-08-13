open Ast

(* 寄存器分类 *)
type reg_type =
  | CallerSaved   (* 调用者保存寄存器 *)
  | CalleeSaved   (* 被调用者保存寄存器 *)
  | TempReg       (* 临时寄存器 *)

(* 上下文类型 *)
type context = {
    current_func: string;          (* 当前函数名 *)
    local_offset: int;             (* 局部变量区当前偏移量 *)
    frame_size: int;               (* 栈帧总大小（计算后设置） *)
    var_offset: (string * int) list list; (* 符号表栈：每个作用域是一个(string*int)的列表 *)
    label_counter: int;            (* 标签计数器 *)
    loop_stack: (string * string) list; (* 循环标签栈 (begin_label, end_label) *)
    saved_regs: string list;       (* 需要保存的寄存器列表 *)
    reg_map: (string * reg_type) list; (* 寄存器映射 *)
    param_count: int;              (* 当前参数计数 *)
    temp_regs_used: int;           (* 已使用的临时寄存器数量 *)
    saved_area_size: int;          (* 保存区域大小（包含RA和保存的寄存器） *)
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
    (* 初始保存区域大小：RA(4字节) + 所有被调用者保存寄存器(12*4=48字节) *)
    { current_func = func_name;
      local_offset = 0;
      frame_size = 0;
      var_offset = [[]];  (* 初始化为一个作用域（空列表） *)
      label_counter = 0;
      loop_stack = [];
      saved_regs = ["s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11"];
      reg_map = reg_map;
      param_count = 0;
      temp_regs_used = 0;
      saved_area_size = 52 } (* 4(ra) + 12*4(regs) = 52 *)

(* 栈对齐常量 *)
let stack_align = 16

(* 获取唯一标签 - 使用函数名作为前缀 *)
let fresh_label ctx prefix =
    let n = ctx.label_counter in
    { ctx with label_counter = n + 1 },
    Printf.sprintf ".L%s_%s%d" ctx.current_func prefix n  (* 添加函数名前缀 *)

(* 获取变量偏移量 - 支持嵌套作用域查找 *)
let get_var_offset ctx name =
    let rec search = function
        | [] -> None
        | scope :: rest ->
            begin try Some (List.assoc name scope)
            with Not_found -> search rest
            end
    in
    match search ctx.var_offset with
    | Some offset -> offset
    | None -> failwith (Printf.sprintf "Undefined variable: %s" name)

(* 添加变量到当前作用域 *)
let add_var ctx name size =
    match ctx.var_offset with
    | current_scope :: rest_scopes ->
        let offset = ctx.saved_area_size + ctx.local_offset in
        (* 将新绑定添加到当前作用域 *)
        let new_scope = (name, offset) :: current_scope in
        (* 更新当前作用域，并更新局部偏移量 *)
        { ctx with
            var_offset = new_scope :: rest_scopes;
            local_offset = ctx.local_offset + size
        }
    | [] -> failwith "No active scope"

(* 分配临时寄存器 *)
let alloc_temp_reg ctx =
    if ctx.temp_regs_used >= 7 then
        failwith "No more temporary registers available";
    let reg = Printf.sprintf "t%d" ctx.temp_regs_used in
    { ctx with temp_regs_used = ctx.temp_regs_used + 1 }, reg

(* 释放临时寄存器 *)
let free_temp_reg ctx =
    { ctx with temp_regs_used = ctx.temp_regs_used - 1 }

(* 计算栈对齐 *)
let align_stack size align =
    let remainder = size mod align in
    if remainder = 0 then size else size + (align - remainder)

(* 函数序言生成 *)
let gen_prologue ctx func =
    (* 总栈大小 = 保存区域 + 局部变量区域 *)
    let total_size = align_stack (ctx.saved_area_size + ctx.local_offset) stack_align in
    (* 生成保存寄存器的汇编代码 - 顺序保存s0-s11，最后保存ra *)
    let save_regs_asm =
        let save_instrs =
            List.mapi (fun i reg ->
                Printf.sprintf "    sw %s, %d(sp)\n" reg (i * 4) (* Added \n *)
            ) ctx.saved_regs
            @ [Printf.sprintf "    sw ra, %d(sp)\n" (List.length ctx.saved_regs * 4)] (* Added \n *)
        in
        String.concat "" save_instrs (* Already has \n in each line *)
    in
    let asm = Printf.sprintf "
    .globl %s
%s:
    addi sp, sp, -%d
%s" func.name func.name total_size save_regs_asm in
    (asm, { ctx with frame_size = total_size })

(* 函数结语生成 *)
let gen_epilogue ctx =
    (* 生成恢复寄存器的汇编代码 - 逆序恢复：先恢复ra，然后s11-s0 *)
    let restore_regs_asm =
        (* 关键修复：按入栈顺序的逆序恢复 *)
        let restore_list =
            ["ra"] @ (List.rev ctx.saved_regs) (* 恢复顺序：ra, s11, s10, ..., s0 *)
        in
        (* 关键修复：偏移量计算与保存时完全匹配 *)
        List.mapi (fun i reg ->
            let offset = (List.length ctx.saved_regs * 4) - (i * 4) in
            Printf.sprintf "    lw %s, %d(sp)\n" reg offset (* Removed leading \n and space, added trailing \n *)
        ) restore_list
        |> String.concat "" (* Already has \n in each line *)
    in

    Printf.sprintf "%s    addi sp, sp, %d\n    ret\n" restore_regs_asm ctx.frame_size

(* 表达式代码生成 *)
let rec gen_expr ctx expr =
    match expr with
    | IntLit n ->
        let (ctx, reg) = alloc_temp_reg ctx in
        (ctx, Printf.sprintf "    li %s, %d\n" reg n, reg) (* Removed leading \n, added trailing \n *)
    | Var name ->
        let offset = get_var_offset ctx name in
        let (ctx, reg) = alloc_temp_reg ctx in
        (ctx, Printf.sprintf "    lw %s, %d(sp)\n" reg offset, reg) (* Added trailing \n *)
    | BinOp (e1, op, e2) ->
        let (ctx, asm1, reg1) = gen_expr ctx e1 in
        let (ctx, asm2, reg2) = gen_expr ctx e2 in
        (* 优化：复用reg1作为目标寄存器，减少寄存器使用 *)
        let reg_dest = reg1 in
        let instr = match op with
        | Add -> Printf.sprintf "add %s, %s, %s\n" reg_dest reg1 reg2
        | Sub -> Printf.sprintf "sub %s, %s, %s\n" reg_dest reg1 reg2
        | Mul -> Printf.sprintf "mul %s, %s, %s\n" reg_dest reg1 reg2
        | Div -> Printf.sprintf "div %s, %s, %s\n" reg_dest reg1 reg2
        | Mod -> Printf.sprintf "rem %s, %s, %s\n" reg_dest reg1 reg2
        | Lt  -> Printf.sprintf "slt %s, %s, %s\n" reg_dest reg1 reg2
        | Le  -> Printf.sprintf "sgt %s, %s, %s\n    xori %s, %s, 1\n" reg_dest reg1 reg2 reg_dest reg_dest
        | Gt  -> Printf.sprintf "sgt %s, %s, %s\n" reg_dest reg1 reg2
        | Ge  -> Printf.sprintf "slt %s, %s, %s\n    xori %s, %s, 1\n" reg_dest reg1 reg2 reg_dest reg_dest
        | Eq  -> Printf.sprintf "sub %s, %s, %s\n    seqz %s, %s\n" reg_dest reg1 reg2 reg_dest reg_dest
        | Ne  -> Printf.sprintf "sub %s, %s, %s\n    snez %s, %s\n" reg_dest reg1 reg2 reg_dest reg_dest
        | And -> Printf.sprintf "and %s, %s, %s\n" reg_dest reg1 reg2
        | Or  -> Printf.sprintf "or %s, %s, %s\n" reg_dest reg1 reg2
        in
        (* 修正：只释放reg2，因为reg1被复用为结果寄存器 *)
        let ctx = free_temp_reg ctx in
        (ctx, asm1 ^ asm2 ^ "    " ^ instr, reg_dest) (* Removed extra \n *)
    | UnOp (op, e) ->
        let (ctx, asm, reg) = gen_expr ctx e in
        (* 优化：直接在源寄存器上操作，无需新寄存器 *)
        let reg_dest = reg in
        let instr = match op with
        | UPlus  -> "" (* mv a, a is a no-op *)
        | UMinus -> Printf.sprintf "neg %s, %s\n" reg_dest reg
        | Not    -> Printf.sprintf "seqz %s, %s\n" reg_dest reg
        in
        let full_asm = if instr = "" then asm else asm ^ "    " ^ instr in (* Removed extra \n *)
        (ctx, full_asm, reg_dest)
    | FuncCall (name, args) ->
        (* 保存当前临时寄存器使用状态，因为参数评估会使用临时寄存器 *)
        let current_temp_regs_state = ctx.temp_regs_used in
        (* 为参数评估创建一个新的上下文，临时寄存器计数从0开始 *)
        let ctx_for_args_eval = { ctx with temp_regs_used = 0 } in

        (* 评估所有参数表达式，获取参数汇编和寄存器列表 *)
        let (ctx_after_args_eval, arg_asm, arg_regs) = gen_args ctx_for_args_eval args in

        (* 恢复临时寄存器使用状态，参数寄存器现在已转移到a寄存器或栈上，可以被“回收” *)
        let ctx_after_args_reset = { ctx_after_args_eval with temp_regs_used = current_temp_regs_state } in

        (* 计算需要为保存临时寄存器和栈传递参数预留的栈空间 *)
        let n_extra = max (List.length args - 8) 0 in
        (* 7个t寄存器 (7*4=28字节) + 栈传递的参数 *)
        let temp_save_area_size = 7 * 4 in
        let total_temp_space = temp_save_area_size + n_extra * 4 in
        let aligned_temp_space = align_stack total_temp_space stack_align in

        (* 调整栈指针以分配临时空间 *)
        let stack_adj_asm =
          if aligned_temp_space > 0 then
            Printf.sprintf "    addi sp, sp, -%d\n" aligned_temp_space
          else ""
        in

        (* 保存调用者保存寄存器 (t0-t6) 到栈上，只保存实际使用的 *)
        let save_temps_asm =
          List.mapi (fun i reg_name -> (* 这里的 reg_name 就是 "t0", "t1" 等 *)
            if i < current_temp_regs_state then
                Printf.sprintf "    sw %s, %d(sp)\n" reg_name (i * 4) (* 使用 reg_name *)
            else ""
          ) (List.init 7 (fun i -> Printf.sprintf "t%d" i))
          |> String.concat ""
        in

        (* 移动参数到正确位置 (a0-a7 或栈) *)
        let move_args_asm =
          let rec move_args regs index asm =
            match regs with
            | [] -> asm
            | reg::rest when index < 8 ->
                let target = Printf.sprintf "a%d" index in
                let new_asm = if reg = target then asm else
                    asm ^ Printf.sprintf "    mv %s, %s\n" target reg
                in
                move_args rest (index+1) new_asm
            | reg::rest ->
                (* 栈传递参数的偏移量：在临时寄存器保存区之上 *)
                let stack_offset = temp_save_area_size + (index - 8) * 4 in
                move_args rest (index+1)
                  (asm ^ Printf.sprintf "    sw %s, %d(sp)\n" reg stack_offset)
          in
          move_args arg_regs 0 ""
        in

        (* 函数调用 *)
        let call_asm = Printf.sprintf "    call %s\n" name in

        (* 恢复调用者保存寄存器 (t0-t6)，只恢复之前保存的 *)
        let restore_temps_asm =
          List.mapi (fun i reg_name -> (* 这里的 reg_name 就是 "t0", "t1" 等 *)
            if i < current_temp_regs_state then
                Printf.sprintf "    lw %s, %d(sp)\n" reg_name (i * 4) (* 使用 reg_name *)
            else ""
          ) (List.init 7 (fun i -> Printf.sprintf "t%d" i))
          |> String.concat ""
        in

        (* 恢复栈指针 *)
        let restore_stack_asm =
          if aligned_temp_space > 0 then
            Printf.sprintf "    addi sp, sp, %d\n" aligned_temp_space
          else ""
        in

        (* 将返回值 (a0) 移动到目标寄存器 *)
        let (ctx_final, reg_dest) = alloc_temp_reg ctx_after_args_reset in
        let move_result = Printf.sprintf "    mv %s, a0\n" reg_dest in

        (* 组合汇编代码 *)
        let asm = arg_asm ^ stack_adj_asm ^ save_temps_asm ^
                  move_args_asm ^ call_asm ^
                  restore_temps_asm ^ restore_stack_asm ^
                  move_result in

        (ctx_final, asm, reg_dest)

(* 生成参数代码 - 返回参数寄存器列表 *)
and gen_args ctx args =
  let rec process_args ctx asm regs count = function
    | [] -> (ctx, asm, List.rev regs)
    | arg::rest ->
        let (ctx, arg_asm, reg) = gen_expr ctx arg in
        let new_asm = asm ^ arg_asm in
        process_args ctx new_asm (reg::regs) (count+1) rest
  in
  process_args ctx "" [] 0 args

(* 处理语句列表的辅助函数 *)
let rec gen_stmts ctx stmts =
    List.fold_left (fun (ctx, asm) stmt ->
        let (ctx', stmt_asm) = gen_stmt ctx stmt in
        (ctx', asm ^ stmt_asm) (* Removed extra \n *)
    ) (ctx, "") stmts

(* 语句代码生成 *)
and gen_stmt ctx stmt =
    match stmt with
    | Block stmts ->
        (* 进入新作用域：压入一个新的空作用域 *)
        let new_ctx = { ctx with var_offset = [] :: ctx.var_offset } in
        let (ctx_after, asm) = gen_stmts new_ctx stmts in
        (* 离开作用域：弹出当前作用域 *)
        let popped_ctx =
            match ctx_after.var_offset with
            | _ :: outer_scopes -> { ctx_after with var_offset = outer_scopes }
            | [] -> failwith "Scope stack underflow"
        in
        (popped_ctx, asm)

    | VarDecl (name, expr) ->
        let (ctx, expr_asm, reg) = gen_expr ctx expr in
        let ctx = add_var ctx name 4 in
        let offset = get_var_offset ctx name in
        let asm = expr_asm ^ Printf.sprintf "    sw %s, %d(sp)\n" reg offset in (* Removed leading \n, added trailing \n *)
        (free_temp_reg ctx, asm)

    | VarAssign (name, expr) ->
        let offset = get_var_offset ctx name in
        let (ctx, expr_asm, reg) = gen_expr ctx expr in
        let asm = expr_asm ^ Printf.sprintf "    sw %s, %d(sp)\n" reg offset in (* Removed leading \n, added trailing \n *)
        (free_temp_reg ctx, asm)

    | If (cond, then_stmt, else_stmt) ->
        (* 1. 生成条件表达式 *)
        let (ctx_after_cond_expr, cond_asm, cond_reg) = gen_expr ctx cond in

        (* 2. 生成 if-else 结构所需的标签，从 ctx_after_cond_expr 开始递增 *)
        let (ctx_with_else_label, else_label) = fresh_label ctx_after_cond_expr "if_else" in
        let (ctx_with_end_label, end_label) = fresh_label ctx_with_else_label "if_end" in

        (* 3. 生成 'then' 分支的代码，使用 ctx_with_end_label 作为起始上下文 *)
        let (ctx_after_then_branch, then_asm) = gen_stmt ctx_with_end_label then_stmt in

        let final_asm, final_ctx =
            match else_stmt with
            | Some s ->
                (* 4. 生成 'else' 分支的代码，从 ctx_after_then_branch 开始，确保标签计数器连续 *)
                let (ctx_after_else_branch, else_asm) = gen_stmt ctx_after_then_branch s in
                (
                    cond_asm ^
                    Printf.sprintf "    beqz %s, %s\n" cond_reg else_label ^
                    then_asm ^
                    Printf.sprintf "    j %s\n" end_label ^
                    Printf.sprintf "%s:\n" else_label ^
                    else_asm ^
                    Printf.sprintf "%s:\n" end_label,
                    ctx_after_else_branch (* 最终上下文是 else 分支之后的上下文 *)
                )
            | None ->
                (
                    cond_asm ^
                    Printf.sprintf "    beqz %s, %s\n" cond_reg end_label ^
                    then_asm ^
                    Printf.sprintf "%s:\n" end_label,
                    ctx_after_then_branch (* 最终上下文是 then 分支之后的上下文 *)
                )
        in
        (* 5. 释放条件表达式使用的临时寄存器 *)
        (free_temp_reg final_ctx, final_asm)

    | While (cond, body) ->
        let (ctx_before_loop_labels, begin_label) = fresh_label ctx "loop_begin" in
        let (ctx_with_loop_labels, end_label) = fresh_label ctx_before_loop_labels "loop_end" in

        (* 生成条件表达式，使用包含循环标签的上下文 *)
        let (ctx_after_cond_expr, cond_asm, cond_reg) = gen_expr ctx_with_loop_labels cond in

        let loop_ctx = { ctx_after_cond_expr with
            loop_stack = (begin_label, end_label) :: ctx_after_cond_expr.loop_stack } in
        let (ctx_after_body, body_asm) = gen_stmt loop_ctx body in

        (* 仅弹出循环栈，保留其他字段 *)
        let ctx_after_loop = { ctx_after_body with
            loop_stack = List.tl ctx_after_body.loop_stack } in

        let asm = Printf.sprintf "%s:\n" begin_label ^ (* Added \n *)
                cond_asm ^
                Printf.sprintf "    beqz %s, %s\n" cond_reg end_label ^
                body_asm ^
                Printf.sprintf "    j %s\n" begin_label ^
                Printf.sprintf "%s:\n" end_label in (* Added \n *)
        (free_temp_reg ctx_after_loop, asm)

    | Break ->
        (match ctx.loop_stack with
        | (_, end_label)::_ ->
            (ctx, Printf.sprintf "    j %s\n" end_label) (* Added \n *)
        | [] -> failwith "break outside loop")

    | Continue ->
        (match ctx.loop_stack with
        | (begin_label, _)::_ ->
            (ctx, Printf.sprintf "    j %s\n" begin_label) (* Added \n *)
        | [] -> failwith "continue outside loop")

  | Return expr_opt ->
        let (ctx_after_expr, expr_asm, _reg) =
            match expr_opt with
            | Some expr ->
                let (ctx_e, asm_e, r) = gen_expr ctx expr in
                if r = "a0" then (ctx_e, asm_e, r)
                else (ctx_e, asm_e ^ Printf.sprintf "    mv a0, %s\n" r, "a0") (* Removed leading \n, added trailing \n *)
            | None -> (ctx, "", "a0")
        in
        (* 关键修复：在返回语句后直接跳转到函数结尾 *)
        let epilogue_asm = gen_epilogue ctx_after_expr in (* Use ctx_after_expr for epilogue *)
        (free_temp_reg ctx_after_expr, expr_asm ^ epilogue_asm) (* Removed extra \n *)
    | EmptyStmt -> (ctx, "")
    | ExprStmt e ->
        let (ctx, asm, _) = gen_expr ctx e in
        (free_temp_reg ctx, asm)

(* 函数代码生成 *)
let gen_function func =
    let ctx = create_context func.name in

    (* 处理参数 - 在局部变量区分配空间 *)
    let ctx_with_params_offset =
        List.fold_left (fun current_ctx param ->
            add_var current_ctx param 4
        ) ctx func.params
    in

    (* 生成函数序言 *)
    let (prologue_asm, ctx_after_prologue) = gen_prologue ctx_with_params_offset func in

    (* 保存参数到局部变量区 *)
    let save_params_asm, ctx_after_param_saves =
        let rec gen_save_rec current_ctx params index asm =
            match params with
            | [] -> (asm, current_ctx)
            | param::rest ->
                let offset = get_var_offset current_ctx param in (* 局部变量区的偏移量 *)
                if index < 8 then (
                    (* 寄存器参数 *)
                    let reg = Printf.sprintf "a%d" index in
                    gen_save_rec current_ctx rest (index + 1)
                        (asm ^ Printf.sprintf "    sw %s, %d(sp)\n" reg offset)
                ) else (
                    (* 栈参数：位于调用者栈帧中，在当前栈帧之上 *)
                    let caller_stack_offset = ctx_after_prologue.frame_size + (index - 8) * 4 in
                    let (ctx_with_tmp_reg, tmp_reg) = alloc_temp_reg current_ctx in  (* 使用临时寄存器 *)
                    let load_asm = Printf.sprintf "    lw %s, %d(sp)\n" tmp_reg caller_stack_offset in (* Removed leading \n *)
                    let store_asm = Printf.sprintf "    sw %s, %d(sp)\n" tmp_reg offset in (* Added trailing \n *)
                    let ctx_after_free = free_temp_reg ctx_with_tmp_reg in (* 立即释放临时寄存器 *)
                    gen_save_rec ctx_after_free rest (index + 1)
                        (asm ^ load_asm ^ store_asm)
                )
        in
        gen_save_rec ctx_after_prologue func.params 0 ""
    in

    (* 更新上下文为参数保存后的上下文 *)
    let ctx_for_body = ctx_after_param_saves in

    (* 生成函数体：直接处理语句列表（不额外添加作用域） *)
    let (_, body_asm) =
        match func.body with
        | Block stmts -> gen_stmts ctx_for_body stmts
        | _ -> gen_stmt ctx_for_body func.body
    in

    (* 生成函数结语 *)
    let epilogue_asm = gen_epilogue ctx_for_body in

    prologue_asm ^ save_params_asm ^ body_asm ^ epilogue_asm

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