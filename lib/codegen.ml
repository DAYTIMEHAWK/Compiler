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
    next_temp: int;                (* 下一个临时寄存器编号 (unused, but kept from original) *)
    label_counter: int;            (* 标签计数器 *)
    loop_stack: (string * string) list; (* 循环标签栈 (begin_label, end_label) *)
    saved_regs: string list;       (* 需要保存的寄存器列表 (Callee-saved) *)
    reg_map: (string * reg_type) list; (* 寄存器映射 (unused, but kept from original) *)
    param_count: int;              (* 当前参数计数 (unused, but kept from original) *)
    temp_regs_used: int;           (* 已使用的临时寄存器数量 (t0-t6) *)
    saved_area_size: int;          (* 保存区域大小（包含RA和保存的寄存器） *)
}

(* 创建新上下文 *)
let create_context func_name =
    let reg_map = [ (* This map is not actively used in alloc/free, but kept for context *)
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
      next_temp = 0; (* Unused *)
      label_counter = 0;
      loop_stack = [];
      saved_regs = ["s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11"];
      reg_map = reg_map; (* Unused *)
      param_count = 0; (* Unused *)
      temp_regs_used = 0;
      saved_area_size = 4 + (List.length ["s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11"]) * 4 } (* 4(ra) + 12*4(regs) = 52 *)

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
    if ctx.temp_regs_used <= 0 then
        failwith "Attempted to free a temporary register when none are in use";
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
        let ra_offset = (List.length ctx.saved_regs) * 4 in
        let save_instrs = 
            List.mapi (fun i reg -> 
                Printf.sprintf "    sw %s, %d(sp)" reg (i * 4)
            ) ctx.saved_regs
            @ [Printf.sprintf "    sw ra, %d(sp)" ra_offset]
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
    (* 生成恢复寄存器的汇编代码 - 逆序恢复：先恢复ra，然后s11-s0 *)
    let restore_regs_asm = 
        let ra_offset = (List.length ctx.saved_regs) * 4 in
        let restore_ra_instr = Printf.sprintf "    lw ra, %d(sp)" ra_offset in
        let restore_s_regs_instrs = 
            List.mapi (fun i reg ->
                Printf.sprintf "    lw %s, %d(sp)" reg (i * 4)
            ) ctx.saved_regs
        in
        String.concat "\n" (restore_s_regs_instrs @ [restore_ra_instr])
    in
    
    Printf.sprintf "
%s
    addi sp, sp, %d
    ret
" restore_regs_asm ctx.frame_size

(* 表达式代码生成 *)
let rec gen_expr ctx expr =
    match expr with
    | IntLit n -> 
        let (ctx, reg) = alloc_temp_reg ctx in
        (ctx, Printf.sprintf "    li %s, %d" reg n, reg)
    | Var name ->
        let offset = get_var_offset ctx name in
        let (ctx, reg) = alloc_temp_reg ctx in
        (ctx, Printf.sprintf "    lw %s, %d(sp)" reg offset, reg)
    | BinOp (e1, op, e2) ->
        let (ctx, asm1, reg1) = gen_expr ctx e1 in
        let (ctx, asm2, reg2) = gen_expr ctx asm1 e2 in (* Pass ctx with reg1 active *)
        let (ctx, reg_dest) = alloc_temp_reg ctx in
        let instr = match op with
        | Add -> Printf.sprintf "add %s, %s, %s" reg_dest reg1 reg2
        | Sub -> Printf.sprintf "sub %s, %s, %s" reg_dest reg1 reg2
        | Mul -> Printf.sprintf "mul %s, %s, %s" reg_dest reg1 reg2
        | Div -> Printf.sprintf "div %s, %s, %s" reg_dest reg1 reg2
        | Mod -> Printf.sprintf "rem %s, %s, %s" reg_dest reg1 reg2
        | Lt  -> Printf.sprintf "slt %s, %s, %s" reg_dest reg1 reg2
        | Le  -> Printf.sprintf "slt %s, %s, %s\n    xori %s, %s, 1" reg_dest reg2 reg1 reg_dest reg_dest
        | Gt  -> Printf.sprintf "slt %s, %s, %s" reg_dest reg2 reg1
        | Ge  -> Printf.sprintf "slt %s, %s, %s\n    xori %s, %s, 1" reg_dest reg1 reg2 reg_dest reg_dest
        | Eq  -> Printf.sprintf "sub %s, %s, %s\n    seqz %s, %s" reg_dest reg1 reg2 reg_dest reg_dest
        | Ne  -> Printf.sprintf "sub %s, %s, %s\n    snez %s, %s" reg_dest reg1 reg2 reg_dest reg_dest
        | And -> Printf.sprintf "and %s, %s, %s" reg_dest reg1 reg2
        | Or  -> Printf.sprintf "or %s, %s, %s" reg_dest reg1 reg2
        in
        (* Free the operand registers after their values are used *)
        let ctx = free_temp_reg (free_temp_reg ctx) in
        (ctx, asm1 ^ "\n" ^ asm2 ^ "\n    " ^ instr, reg_dest)
    | UnOp (op, e) ->
        let (ctx, asm, reg) = gen_expr ctx e in
        let (ctx, reg_dest) = alloc_temp_reg ctx in
        let instr = match op with
        | UPlus  -> Printf.sprintf "mv %s, %s" reg_dest reg
        | UMinus -> Printf.sprintf "neg %s, %s" reg_dest reg
        | Not    -> Printf.sprintf "seqz %s, %s" reg_dest reg
        in
        (* Free the operand register *)
        let ctx = free_temp_reg ctx in
        (ctx, asm ^ "\n    " ^ instr, reg_dest)
    | FuncCall (name, args) ->
        (* Calculate space needed for stack arguments (if any) and saved temporaries *)
        let n_extra_args = max 0 (List.length args - 8) in
        (* Space for t0-t6 (7 regs) + stack-passed arguments *)
        let temp_and_arg_spill_size = (7 * 4) + (n_extra_args * 4) in
        let aligned_temp_and_arg_spill_size = align_stack temp_and_arg_spill_size stack_align in
        
        (* Adjust stack pointer for saving temps and spilling args *)
        let stack_adj_asm = 
            if aligned_temp_and_arg_spill_size > 0 then 
                Printf.sprintf "    addi sp, sp, -%d\n" aligned_temp_and_arg_spill_size
            else ""
        in
        
        (* Save temporary registers (t0-t6) *)
        let save_temps_asm = 
            List.init 7 (fun i -> 
                Printf.sprintf "    sw t%d, %d(sp)" i (i * 4))
            |> String.concat "\n"
        in
        
        (* Generate code for arguments and move them to a0-a7 or stack *)
        (* gen_args now directly handles moving to aX or stack, freeing temps as it goes *)
        let (ctx_after_args, arg_setup_asm) = gen_args ctx args in
        
        (* Function call *)
        let call_asm = Printf.sprintf "    call %s\n" name in
        
        (* Restore temporary registers (t0-t6) *)
        let restore_temps_asm = 
            List.init 7 (fun i -> 
                Printf.sprintf "    lw t%d, %d(sp)" i (i * 4))
            |> String.concat "\n"
        in
        
        (* Restore stack pointer *)
        let restore_stack_asm = 
            if aligned_temp_and_arg_spill_size > 0 then 
                Printf.sprintf "    addi sp, sp, %d" aligned_temp_and_arg_spill_size
            else ""
        in
        
        (* Get return value *)
        let (ctx_final, reg_dest) = alloc_temp_reg ctx_after_args in (* Allocate a fresh temp for the result *)
        let move_result = Printf.sprintf "    mv %s, a0" reg_dest in
        
        (* Combine all ASM *)
        let asm = stack_adj_asm ^ save_temps_asm ^ "\n" ^ 
                  arg_setup_asm ^ call_asm ^ "\n" ^ 
                  restore_temps_asm ^ "\n" ^ restore_stack_asm ^ "\n" ^ 
                  move_result in
        
        (ctx_final, asm, reg_dest)

(* Generate argument code: directly move to aX or spill to stack *)
and gen_args ctx args =
  let rec process_args ctx asm index = function
    | [] -> (ctx, asm)
    | arg_expr::rest ->
        let (ctx_after_expr, arg_asm, reg) = gen_expr ctx arg_expr in
        (* Free the temporary register used for this argument's value immediately *)
        let ctx_freed = free_temp_reg ctx_after_expr in 
        
        let move_instr =
          if index < 8 then (* Argument fits in a0-a7 *)
            Printf.sprintf "    mv a%d, %s\n" index reg
          else (* Argument needs to be spilled to stack *)
            (* Stack arguments are placed after the saved t-registers (7*4 = 28 bytes) *)
            let stack_offset = 28 + (index - 8) * 4 in
            Printf.sprintf "    sw %s, %d(sp)\n" reg stack_offset
        in
        process_args ctx_freed (asm ^ arg_asm ^ "\n" ^ move_instr) (index+1) rest
  in
  process_args ctx "" 0 args

(* 处理语句列表的辅助函数 *)
let rec gen_stmts ctx stmts =
    List.fold_left (fun (ctx, asm) stmt ->
        let (ctx', stmt_asm) = gen_stmt ctx stmt in
        (ctx', asm ^ "\n" ^ stmt_asm)
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
        let asm = expr_asm ^ Printf.sprintf "\n    sw %s, %d(sp)" reg offset in
        (free_temp_reg ctx, asm)
    
    | VarAssign (name, expr) ->
        let offset = get_var_offset ctx name in
        let (ctx, expr_asm, reg) = gen_expr ctx expr in
        let asm = expr_asm ^ Printf.sprintf "\n    sw %s, %d(sp)" reg offset in
        (free_temp_reg ctx, asm)
    
    | If (cond, then_stmt, else_stmt) ->
        let (ctx, cond_asm, cond_reg) = gen_expr ctx cond in
        let (ctx_after_cond_free) = free_temp_reg ctx in (* Free condition register *)
        
        let (ctx_then, then_label) = fresh_label ctx_after_cond_free "if_then" in
        let (ctx_else, else_label) = fresh_label ctx_then "if_else" in
        let (ctx_end, end_label) = fresh_label ctx_else "if_end" in
        
        let (ctx_after_then, then_asm) = gen_stmt ctx_end then_stmt in
        let (ctx_after_else, else_asm) = match else_stmt with
            | Some s -> gen_stmt ctx_after_then s
            | None -> (ctx_after_then, "") in
        
        let asm = cond_asm ^
                Printf.sprintf "\n    beqz %s, %s" cond_reg else_label ^
                Printf.sprintf "\n%s:" then_label ^ (* Then block starts here *)
                then_asm ^
                Printf.sprintf "\n    j %s" end_label ^
                Printf.sprintf "\n%s:" else_label ^
                else_asm ^
                Printf.sprintf "\n%s:" end_label in
        (ctx_after_else, asm)
    
    | While (cond, body) ->
        let (ctx_begin, begin_label) = fresh_label ctx "loop_begin" in
        let (ctx_end, end_label) = fresh_label ctx_begin "loop_end" in
        
        let (ctx_cond_eval, cond_asm, cond_reg) = gen_expr ctx_end cond in
        let ctx_cond_freed = free_temp_reg ctx_cond_eval in (* Free condition register *)
        
        let loop_ctx = { ctx_cond_freed with 
            loop_stack = (begin_label, end_label) :: ctx_cond_freed.loop_stack } in
        let (ctx_after_body, body_asm) = gen_stmt loop_ctx body in
        
        (* Only pop loop stack, keep other fields *)
        let ctx_after_loop = { ctx_after_body with 
            loop_stack = List.tl ctx_after_body.loop_stack } in
        
        let asm = Printf.sprintf "%s:" begin_label ^
                cond_asm ^
                Printf.sprintf "\n    beqz %s, %s" cond_reg end_label ^
                body_asm ^
                Printf.sprintf "\n    j %s" begin_label ^
                Printf.sprintf "\n%s:" end_label in
        (ctx_after_loop, asm)
    
    | Break ->
        (match ctx.loop_stack with
        | (_, end_label)::_ -> 
            (ctx, Printf.sprintf "    j %s" end_label)
        | [] -> failwith "break outside loop")
    
    | Continue ->
        (match ctx.loop_stack with
        | (begin_label, _)::_ -> 
            (ctx, Printf.sprintf "    j %s" begin_label)
        | [] -> failwith "continue outside loop")
    
    | Return expr_opt ->
        let (ctx_after_expr, expr_asm, _reg) = 
            match expr_opt with
            | Some expr -> 
                let (ctx_e, asm_e, r) = gen_expr ctx expr in
                if r = "a0" then (ctx_e, asm_e, r)
                else (ctx_e, asm_e ^ Printf.sprintf "\n    mv a0, %s" r, "a0")
            | None -> (ctx, "", "a0")
        in
        let ctx_freed = match expr_opt with
            | Some _ -> free_temp_reg ctx_after_expr
            | None -> ctx_after_expr
        in
        (* Generate epilogue and return *)
        let epilogue_asm = gen_epilogue ctx_freed in
        (ctx_freed, expr_asm ^ "\n" ^ epilogue_asm)
    | EmptyStmt -> (ctx, "")
    | ExprStmt e -> 
        let (ctx, asm, _) = gen_expr ctx e in 
        (free_temp_reg ctx, asm)

(* 函数代码生成 *)
let gen_function func =
    let ctx = create_context func.name in
    
    (* 处理参数 - 在局部变量区分配空间 *)
    let ctx = 
        List.fold_left (fun ctx param ->
            add_var ctx param 4
        ) ctx func.params
    in
    
    (* 生成函数序言 *)
    let (prologue_asm, ctx_after_prologue) = gen_prologue ctx func in
    
    (* 保存参数到局部变量区 *)
    let save_params_asm = 
        let rec gen_save params index asm =
            match params with
            | [] -> asm
            | param::rest ->
                let offset = get_var_offset ctx_after_prologue param in (* Offset of local variable slot *)
                if index < 8 then (
                    (* Register parameters (a0-a7) *)
                    let reg = Printf.sprintf "a%d" index in
                    gen_save rest (index + 1) 
                        (asm ^ Printf.sprintf "    sw %s, %d(sp)\n" reg offset)
                ) else (
                    (* Stack parameters: loaded from caller's frame, relative to current sp *)
                    (* The frame_size is the total size of the current function's stack frame.
                       The stack arguments are located *above* the stack pointer after the prologue.
                       The first stack argument (arg8) is at `frame_size + 0*4(sp)`.
                       The second stack argument (arg9) is at `frame_size + 1*4(sp)`.
                       ...
                    *)
                    let param_load_offset = ctx_after_prologue.frame_size + (index - 8) * 4 in
                    let (ctx_temp, reg_temp) = alloc_temp_reg ctx_after_prologue in (* Use a temp reg to load *)
                    let load_instr = Printf.sprintf "    lw %s, %d(sp)\n" reg_temp param_load_offset in
                    let store_instr = Printf.sprintf "    sw %s, %d(sp)" reg_temp offset in
                    let ctx_freed = free_temp_reg ctx_temp in (* Free the temp reg after use *)
                    gen_save rest (index + 1) 
                        (asm ^ load_instr ^ store_instr ^ "\n")
                )
        in
        gen_save func.params 0 ""
    in
    
    (* 生成函数体：直接处理语句列表（不额外添加作用域，因为参数已经在初始作用域处理） *)
    let (_, body_asm) = 
        match func.body with
        | Block stmts -> gen_stmts ctx_after_prologue stmts
        | _ -> gen_stmt ctx_after_prologue func.body
    in
    
    (* 生成函数结语 *)
    let epilogue_asm = gen_epilogue ctx_after_prologue in
    
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