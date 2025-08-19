(* codegen.ml *)
open Ast

(* 寄存器分类 *)
type reg_type = 
  | CallerSaved   (* 调用者保存寄存器 *)
  | CalleeSaved   (* 被调用者保存寄存器 *)
  | TempReg       (* 临时寄存器 *)

(* 上下文类型 *)
type context = {
    current_func: string;
    local_offset: int;
    frame_size: int;
    var_offset: (string * int) list list;
    next_temp: int;
    label_counter: int;
    loop_stack: (string * string * string) list;  (* (begin_label, next_label, end_label) *)
    saved_regs: string list;
    reg_map: (string * reg_type) list;
    param_count: int;
    used_regs: string list;  (* 跟踪正在使用的寄存器 *)
    saved_area_size: int;
    max_local_offset: int;
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
      local_offset = 0;
      frame_size = 0;
      var_offset = [[]];
      next_temp = 0;
      label_counter = 0;
      loop_stack = [];
      saved_regs = ["s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11"];
      reg_map = reg_map;
      param_count = 0;
      used_regs = [];  (* 初始化为空列表 *)
      max_local_offset = 0; 
      saved_area_size = 52 } (* 4(ra) + 12*4(regs) = 52 *)

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
      let offset = ctx.saved_area_size + ctx.local_offset in
      let new_scope = (name, offset) :: current_scope in
      { ctx with 
          var_offset = new_scope :: rest_scopes;
          local_offset = ctx.local_offset + size;
          max_local_offset = max ctx.max_local_offset (ctx.local_offset + size)
      }
  | [] -> failwith "No active scope"

(* 改进的寄存器分配函数 *)
let alloc_temp_reg ctx =
    let temp_regs = ["t0"; "t1"; "t2"; "t3"; "t4"; "t5"; "t6"] in
    let saved_regs_list = ["s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11"] in
    let all_regs = temp_regs @ saved_regs_list in
    
    (* 找到第一个未被使用的寄存器 *)
    let available_reg = List.find_opt (fun reg -> 
        not (List.mem reg ctx.used_regs)) all_regs in
    
    match available_reg with
    | Some reg -> 
        { ctx with used_regs = reg :: ctx.used_regs }, reg
    | None ->
        (* 所有寄存器都被使用，溢出到栈 *)
        let spill_offset = ctx.saved_area_size + ctx.max_local_offset + (List.length ctx.used_regs) * 4 in
        let spill_reg = Printf.sprintf "SPILL_%d" spill_offset in
        { ctx with used_regs = spill_reg :: ctx.used_regs }, spill_reg

(* 改进的寄存器释放函数 *)
let free_temp_reg ctx reg =
    { ctx with used_regs = List.filter (fun r -> r <> reg) ctx.used_regs }

(* 计算栈对齐 *)
let align_stack size align =
    let remainder = size mod align in
    if remainder = 0 then size else size + (align - remainder)

(* 函数序言生成 *)
let gen_prologue ctx func =
    let estimated_locals = 
        match func.name with
        | "main" -> 500
        | _ -> 200
    in
    let total_size = align_stack (ctx.saved_area_size + estimated_locals) stack_align in
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
        let ra_restore = Printf.sprintf "    lw ra, %d(sp)" (List.length ctx.saved_regs * 4) in
        let s_regs_restore = 
            List.rev ctx.saved_regs
            |> List.mapi (fun i reg ->
                let offset = (List.length ctx.saved_regs - 1 - i) * 4 in
                Printf.sprintf "    lw %s, %d(sp)" reg offset)
            |> String.concat "\n" in
        ra_restore ^ "\n" ^ s_regs_restore
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
        failwith "Not a spill register"

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
    
        (* 如果两个寄存器相同，需要分配新寄存器 *)
        let (ctx, reg2, extra_move) = 
            if reg1 = reg2 then
                let (ctx', new_reg) = alloc_temp_reg ctx in
                let move_instr = 
                    if is_spill_reg new_reg then
                        Printf.sprintf "    mv t1, %s\n%s" reg2 (gen_store_spill new_reg "t1")
                    else if is_spill_reg reg2 then
                        Printf.sprintf "%s\n    mv %s, t0" (gen_load_spill reg2 "t0") new_reg
                    else
                        Printf.sprintf "    mv %s, %s" new_reg reg2
                in
                (ctx', new_reg, move_instr)
            else
                (ctx, reg2, "")
        in
    
        (* 处理溢出寄存器 *)
        let load1 = gen_load_spill reg1 "t0" in
        let load2 = gen_load_spill reg2 "t1" in
        let actual_reg1 = if is_spill_reg reg1 then "t0" else reg1 in
        let actual_reg2 = if is_spill_reg reg2 then "t1" else reg2 in
    
        (* 重用第一个寄存器作为目标寄存器 *)
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
                 (if extra_move = "" then [] else [extra_move]) @
                 (if load1 = "" then [] else [load1]) @>
                 (if load2 = "" then [] else [load2]) @>
                 [instr] @>
                 (if store_result = "" then [] else [store_result]) in
        String.concat "\n" (List.filter (fun s -> s <> "") parts) in
    
        (* 释放第二个寄存器 *)
        let ctx = free_temp_reg ctx reg2 in
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
          let parts = [asm] @>
                     (if load_asm = "" then [] else [load_asm]) @>
                     [instr] @>
                     (if store_asm = "" then [] else [store_asm]) in
          String.concat "\n" (List.filter (fun s -> s <> "") parts) in
        (ctx, full_asm, reg)

    | FuncCall (name, args) ->
    let (ctx, arg_asm, arg_regs) = gen_args ctx args in
    
    let n_extra = max (List.length args - 8) 0 in
    let temp_space = 28 + n_extra * 4 in
    let aligned_temp_space = align_stack temp_space stack_align in
    
    let stack_adj_asm = 
      if aligned_temp_space > 0 then 
        Printf.sprintf "    addi sp, sp, -%d\n" aligned_temp_space
      else "" in
    
    let save_temps_asm = 
      List.init 7 (fun i -> 
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
              (if load_src = "" then [] else [load_src]) @>
              (if move_instr = "" then [] else [move_instr]) in
            move_args rest (index+1) new_parts
        | reg::rest ->
            (*
             * 修复：根据RISC-V调用约定，调用者将第9个参数(index=8)放在0(sp)，
             * 第10个(index=9)放在4(sp)，以此类推。
             * 这里的sp是已经为参数和临时寄存器保存区调整过的sp。
             * 原来的偏移计算 28 + ... 是错误的。
             *)
            let stack_offset = (index - 8) * 4 in
            let load_src = gen_load_spill reg "t0" in
            let actual_src = if is_spill_reg reg then "t0" else reg in
            let store_instr = Printf.sprintf "    sw %s, %d(sp)" actual_src stack_offset in
            let new_parts = parts @
              (if load_src = "" then []