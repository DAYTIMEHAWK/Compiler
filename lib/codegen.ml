open Ast

(* 寄存器分类 *)
type reg_type =
  | CallerSaved   (* 调用者保存寄存器 *)
  | CalleeSaved   (* 被调用者保存寄存器 *)
  | TempReg       (* 临时寄存器 *)

(* 上下文类型 *)
type context = {
    current_func: string;          (* 当前函数名 *)
    func_end_label: string;        (* 函数末尾统一出口标签 *)
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
    { current_func = func_name;
      func_end_label = Printf.sprintf ".L%s_epilogue" func_name;
      local_offset = 0;
      frame_size = 0;
      var_offset = [[]];
      label_counter = 0;
      loop_stack = [];
      saved_regs = ["s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11"];
      reg_map = reg_map;
      param_count = 0;
      temp_regs_used = 0;
      saved_area_size = 52 }

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
    | None -> failwith (Printf.sprintf "Undefined variable: %s in function %s" name ctx.current_func)

(* 添加变量到当前作用域 *)
let add_var ctx name size =
    match ctx.var_offset with
    | current_scope :: rest_scopes ->
        let offset = ctx.saved_area_size + ctx.local_offset in
        let new_scope = (name, offset) :: current_scope in
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
    if ctx.temp_regs_used <= 0 then ctx
    else { ctx with temp_regs_used = ctx.temp_regs_used - 1 }

(* 计算栈对齐 *)
let align_stack size align =
    let remainder = size mod align in
    if remainder = 0 then size else size + (align - remainder)

(* 函数序言生成 *)
let gen_prologue ctx func =
    let total_size = align_stack (ctx.saved_area_size + ctx.local_offset) stack_align in
    let save_regs_asm =
        let save_instrs =
            List.mapi (fun i reg ->
                Printf.sprintf "    sw %s, %d(sp)" reg (i * 4)
            ) ctx.saved_regs
            @ [Printf.sprintf "    sw ra, %d(sp)" (List.length ctx.saved_regs * 4)]
        in
        String.concat "\n" save_instrs
    in
    let asm = Printf.sprintf "
    .globl %s
%s:
    addi sp, sp, -%d
%s
" func.name func.name total_size save_regs_asm in
    (asm, { ctx with frame_size = total_size })

(* 函数结语生成 *)
let gen_epilogue ctx =
    let restore_regs_asm =
        let restore_instrs =
            [Printf.sprintf "    lw ra, %d(sp)" (List.length ctx.saved_regs * 4)] @
            List.mapi (fun i reg ->
                Printf.sprintf "    lw %s, %d(sp)" reg (i * 4)
            ) ctx.saved_regs
        in
        String.concat "\n" restore_instrs
    in
    Printf.sprintf "
%s:
%s
    addi sp, sp, %d
    ret
" ctx.func_end_label restore_regs_asm ctx.frame_size

(* 表达式代码生成 *)
let rec gen_expr ctx expr =
    match expr with
    | IntLit n ->
        let (ctx, reg) = alloc_temp_reg ctx in
        (ctx, Printf.sprintf "\n    li %s, %d" reg n, reg)
    | Var name ->
        let offset = get_var_offset ctx name in
        let (ctx, reg) = alloc_temp_reg ctx in
        (ctx, Printf.sprintf "\n    lw %s, %d(sp)" reg offset, reg)
    | BinOp (e1, op, e2) ->
        let (ctx, asm1, reg1) = gen_expr ctx e1 in
        let (ctx, asm2, reg2) = gen_expr ctx e2 in
        let reg_dest = reg1 in
        let instr = match op with
        | Add -> Printf.sprintf "add %s, %s, %s" reg_dest reg1 reg2
        | Sub -> Printf.sprintf "sub %s, %s, %s" reg_dest reg1 reg2
        | Mul -> Printf.sprintf "mul %s, %s, %s" reg_dest reg1 reg2
        | Div -> Printf.sprintf "div %s, %s, %s" reg_dest reg1 reg2
        | Mod -> Printf.sprintf "rem %s, %s, %s" reg_dest reg1 reg2
        | Lt  -> Printf.sprintf "slt %s, %s, %s" reg_dest reg1 reg2
        | Le  -> Printf.sprintf "sgt %s, %s, %s\n    xori %s, %s, 1" reg_dest reg1 reg2 reg_dest reg_dest
        | Gt  -> Printf.sprintf "sgt %s, %s, %s" reg_dest reg1 reg2
        | Ge  -> Printf.sprintf "slt %s, %s, %s\n    xori %s, %s, 1" reg_dest reg1 reg2 reg_dest reg_dest
        | Eq  -> Printf.sprintf "sub %s, %s, %s\n    seqz %s, %s" reg_dest reg1 reg2 reg_dest reg_dest
        | Ne  -> Printf.sprintf "sub %s, %s, %s\n    snez %s, %s" reg_dest reg1 reg2 reg_dest reg_dest
        | And -> Printf.sprintf "and %s, %s, %s" reg_dest reg1 reg2
        | Or  -> Printf.sprintf "or %s, %s, %s" reg_dest reg1 reg2
        in
        let ctx = free_temp_reg ctx in
        (ctx, asm1 ^ asm2 ^ "\n    " ^ instr, reg_dest)
    | UnOp (op, e) ->
        let (ctx, asm, reg) = gen_expr ctx e in
        let reg_dest = reg in
        let instr = match op with
        | UPlus  -> ""
        | UMinus -> Printf.sprintf "\n    neg %s, %s" reg_dest reg
        | Not    -> Printf.sprintf "\n    seqz %s, %s" reg_dest reg
        in
        (ctx, asm ^ instr, reg_dest)
    | FuncCall (name, args) ->
        let (ctx, arg_asm, arg_regs) = gen_args ctx args in
        let n_temps_to_save = ctx.temp_regs_used in
        let save_area_size = n_temps_to_save * 4 in

        let save_temps_asm = List.init n_temps_to_save (fun i ->
            Printf.sprintf "\n    sw t%d, %d(sp)" i (i * 4)) |> String.concat ""
        in
        let restore_temps_asm = List.init n_temps_to_save (fun i ->
            Printf.sprintf "\n    lw t%d, %d(sp)" i (i * 4)) |> String.concat ""
        in

        let move_args_asm =
            List.mapi (fun i reg ->
                if i < 8 then
                    Printf.sprintf "\n    mv a%d, %s" i reg
                else
                    Printf.sprintf "\n    sw %s, %d(sp)" reg (save_area_size + (i - 8) * 4)
            ) arg_regs |> String.concat ""
        in

        let stack_alloc_size = align_stack (save_area_size + (max 0 (List.length args - 8)) * 4) stack_align in
        let alloc_sp_asm = if stack_alloc_size > 0 then Printf.sprintf "\n    addi sp, sp, -%d" stack_alloc_size else "" in
        let free_sp_asm = if stack_alloc_size > 0 then Printf.sprintf "\n    addi sp, sp, %d" stack_alloc_size else "" in

        let call_asm = Printf.sprintf "\n    call %s" name in
        let (ctx, reg_dest) = alloc_temp_reg ctx in
        let move_result_asm = Printf.sprintf "\n    mv %s, a0" reg_dest in

        let asm = arg_asm ^ alloc_sp_asm ^ save_temps_asm ^ move_args_asm ^ call_asm ^ restore_temps_asm ^ free_sp_asm ^ move_result_asm in

        let ctx = List.fold_left (fun c _ -> free_temp_reg c) ctx arg_regs in
        (ctx, asm, reg_dest)

and gen_args ctx args =
  let rec process_args ctx asm regs = function
    | [] -> (ctx, asm, List.rev regs)
    | arg::rest ->
        let (ctx, arg_asm, reg) = gen_expr ctx arg in
        process_args ctx (asm ^ arg_asm) (reg::regs) rest
  in
  process_args ctx "" [] args

and gen_stmts ctx stmts =
    List.fold_left (fun (ctx, asm) stmt ->
        let (ctx', stmt_asm) = gen_stmt ctx stmt in
        (ctx', asm ^ stmt_asm)
    ) (ctx, "") stmts

and gen_stmt ctx stmt =
    match stmt with
    | Block stmts ->
        let new_ctx = { ctx with var_offset = [] :: ctx.var_offset } in
        let (ctx_after, asm) = gen_stmts new_ctx stmts in
        let popped_ctx = { ctx_after with var_offset = List.tl ctx_after.var_offset } in
        (popped_ctx, asm)
    | VarDecl (name, expr) ->
        let (ctx, expr_asm, reg) = gen_expr ctx expr in
        let ctx = add_var ctx name 4 in
        let offset = get_var_offset ctx name in
        let asm = expr_asm ^ Printf.sprintf "\n    sw %s, %d(sp)" reg offset in
        (free_temp_reg ctx, asm)
    | VarAssign (name, expr) ->
        let offset = get_var_offset ctx name in
        let (ctx, expr_asm, reg) = gen_expr ctx expr in
        let asm = expr_asm ^ Printf.sprintf "\n    sw %s, %d(sp)" reg offset in
        (free_temp_reg ctx, asm)
    | If (cond, then_stmt, else_stmt) ->
        let (ctx, cond_asm, cond_reg) = gen_expr ctx cond in
        let (ctx, else_label) = fresh_label ctx "if_else" in
        let (ctx, end_label) = fresh_label ctx "if_end" in
        
        let (ctx_after_then, then_asm) = gen_stmt ctx then_stmt in
        
        let (ctx_final, final_asm) = 
            match else_stmt with
            | Some s ->
                let (ctx_after_else, else_asm) = gen_stmt ctx_after_then s in
                let asm = cond_asm ^
                    Printf.sprintf "\n    beqz %s, %s" cond_reg else_label ^
                    then_asm ^
                    Printf.sprintf "\n    j %s" end_label ^
                    Printf.sprintf "\n%s:" else_label ^
                    else_asm ^
                    Printf.sprintf "\n%s:" end_label
                in
                (ctx_after_else, asm)
            | None ->
                let asm = cond_asm ^
                    Printf.sprintf "\n    beqz %s, %s" cond_reg end_label ^
                    then_asm ^
                    Printf.sprintf "\n%s:" end_label
                in
                (ctx_after_then, asm)
        in
        (free_temp_reg ctx_final, final_asm)

    | While (cond, body) ->
        let (ctx, begin_label) = fresh_label ctx "loop_begin" in
        let (ctx, end_label) = fresh_label ctx "loop_end" in
        let loop_ctx = { ctx with loop_stack = (begin_label, end_label) :: ctx.loop_stack } in
        let (ctx, cond_asm, cond_reg) = gen_expr loop_ctx cond in
        let (_, body_asm) = gen_stmt loop_ctx body in
        let asm =
            Printf.sprintf "\n%s:" begin_label ^
            cond_asm ^
            Printf.sprintf "\n    beqz %s, %s" cond_reg end_label ^
            body_asm ^
            Printf.sprintf "\n    j %s" begin_label ^
            Printf.sprintf "\n%s:" end_label
        in
        (free_temp_reg ctx, asm)
    | Break ->
        (match ctx.loop_stack with
        | (_, end_label)::_ -> (ctx, Printf.sprintf "\n    j %s" end_label)
        | [] -> failwith "break outside loop")
    | Continue ->
        (match ctx.loop_stack with
        | (begin_label, _)::_ -> (ctx, Printf.sprintf "\n    j %s" begin_label)
        | [] -> failwith "continue outside loop")
    | Return expr_opt ->
        let (ctx, expr_asm, reg_opt) =
            match expr_opt with
            | Some expr ->
                let (ctx, asm, r) = gen_expr ctx expr in
                (ctx, asm, Some r)
            | None -> (ctx, "", None)
        in
        let move_asm =
            match reg_opt with
            | Some r when r <> "a0" -> Printf.sprintf "\n    mv a0, %s" r
            | _ -> ""
        in
        let ctx = match reg_opt with Some _ -> free_temp_reg ctx | None -> ctx in
        (ctx, expr_asm ^ move_asm ^ Printf.sprintf "\n    j %s" ctx.func_end_label)
    | EmptyStmt -> (ctx, "")
    | ExprStmt e ->
        let (ctx, asm, _) = gen_expr ctx e in
        (free_temp_reg ctx, asm)

(* 函数代码生成 *)
let gen_function func =
    let ctx = create_context func.name in
    let ctx_with_params =
        List.fold_left (fun c name -> add_var c name 4) ctx func.params
    in
    let (prologue_asm, ctx) = gen_prologue ctx_with_params func in
    let save_params_asm =
        List.mapi (fun i name ->
            let offset = get_var_offset ctx name in
            if i < 8 then
                Printf.sprintf "\n    sw a%d, %d(sp)" i offset
            else
                let stack_offset = ctx.frame_size + (i - 8) * 4 in
                Printf.sprintf "\n    lw t0, %d(sp)\n    sw t0, %d(sp)" stack_offset offset
        ) func.params |> String.concat ""
    in
    let (_, body_asm) = gen_stmt ctx func.body in
    let epilogue_asm = gen_epilogue ctx in
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
