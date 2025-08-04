(* semantic.ml *)

open Ast

exception SemanticError of string

module StringMap = Map.Make(String)

(* 函数信息 *)
type func_info = {
  f_ret_type: string;
  f_param_names: string list;
}

(* 分析上下文 *)
type context = {
  func_table: func_info StringMap.t; (* 全局函数表 *)
  var_scopes: (string StringMap.t) list; (* 变量作用域栈，string -> type ("int") *)
  current_func_ret_type: string; (* 当前函数的返回类型 *)
  in_loop: bool; (* 是否在循环内 *)
}

(* --- 辅助函数 --- *)
let lookup_var name ctx =
  let rec find_in_scopes scopes =
    match scopes with
    | [] -> None
    | current_scope :: outer_scopes ->
        match StringMap.find_opt name current_scope with
        | Some t -> Some t
        | None -> find_in_scopes outer_scopes
  in
  find_in_scopes ctx.var_scopes

let add_var name var_type ctx =
  match ctx.var_scopes with
  | [] -> raise (SemanticError "Cannot declare variable in empty scope") (* Internal error *)
  | current_scope :: outer_scopes ->
      if StringMap.mem name current_scope then
        raise (SemanticError ("Variable '" ^ name ^ "' redeclared in the same scope"))
      else
        let new_current_scope = StringMap.add name var_type current_scope in
        { ctx with var_scopes = new_current_scope :: outer_scopes }

let enter_scope ctx = { ctx with var_scopes = StringMap.empty :: ctx.var_scopes }
let exit_scope ctx = { ctx with var_scopes = List.tl ctx.var_scopes }

(* 表达式和语句的检查函数（互递归） *)
let rec check_expr ctx expr =
  match expr with
  | IntLit _ -> "int"
  | Var name ->
      (match lookup_var name ctx with
      | Some t -> t
      | None -> raise (SemanticError ("Undeclared variable: " ^ name)))
  | BinOp (e1, op, e2) ->
      let t1 = check_expr ctx e1 in
      let t2 = check_expr ctx e2 in
      if t1 <> "int" || t2 <> "int" then
        raise (SemanticError "Operands of binary operator must be integers");
      (match (op, e2) with
      | ((Div | Mod), IntLit 0) -> raise (SemanticError "Division by constant zero")
      | _ -> ());
      "int"
  | UnOp (_, e) -> (* 使用 _ 避免 'unused variable op' 警告 *)
      let t = check_expr ctx e in
      if t <> "int" then
        raise (SemanticError "Operand of unary operator must be an integer");
      "int"
  | FuncCall (name, args) ->
      (match StringMap.find_opt name ctx.func_table with
      | None -> raise (SemanticError ("Undeclared function: " ^ name))
      | Some func_info ->
          let expected_param_count = List.length func_info.f_param_names in
          let actual_param_count = List.length args in
          if expected_param_count <> actual_param_count then
            raise (SemanticError ("Function '" ^ name ^ "' expects " ^ (string_of_int expected_param_count) ^ " arguments, but " ^ (string_of_int actual_param_count) ^ " were given"));
          
          List.iter (fun arg_expr -> 
            if check_expr ctx arg_expr <> "int" then
              raise (SemanticError ("Argument type mismatch in call to '" ^ name ^ "'. All arguments must be integers"))
          ) args;
          
          func_info.f_ret_type)

and check_stmt ctx stmt =
  match stmt with
  | EmptyStmt -> ctx
  
  | ExprStmt e ->
      let _ = check_expr ctx e in
      ctx
      
  | VarDecl (name, init_expr) ->
      let expr_type = check_expr ctx init_expr in
      if expr_type <> "int" then
        raise (SemanticError "Initializer for variable declaration must be an integer");
      add_var name "int" ctx
      
  | VarAssign (name, e) ->
      (match lookup_var name ctx with
      | None -> raise (SemanticError ("Undeclared variable for assignment: " ^ name))
      | Some var_type ->
          if var_type <> "int" then
            raise (SemanticError ("Cannot assign to non-integer variable: " ^ name));
      );
      let expr_type = check_expr ctx e in
      if expr_type = "void" then
        raise (SemanticError "Cannot assign result of a void function");
      if expr_type <> "int" then
        raise (SemanticError ("Type mismatch in assignment to '" ^ name ^ "'"));
      ctx

  | Block stmts ->
      let new_ctx = enter_scope ctx in
      let final_ctx = List.fold_left check_stmt new_ctx stmts in
      exit_scope final_ctx
      
  | If (cond, then_s, else_s_opt) ->
      let cond_type = check_expr ctx cond in
      if cond_type = "void" then
        raise (SemanticError "Condition of if-statement cannot be void");
      
      let _ = check_stmt ctx then_s in
      (match else_s_opt with
      | Some else_s -> let _ = check_stmt ctx else_s in ()
      | None -> ());
      ctx
      
  | While (cond, body) ->
      let cond_type = check_expr ctx cond in
      if cond_type = "void" then
        raise (SemanticError "Condition of while-statement cannot be void");
      
      let loop_ctx = { ctx with in_loop = true } in
      let _ = check_stmt loop_ctx body in
      ctx
      
  | Return e_opt ->
      (match (ctx.current_func_ret_type, e_opt) with
      | "void", Some _ -> raise (SemanticError "A void function cannot return a value")
      | "int", None -> raise (SemanticError "An int function must return a value")
      | "void", None -> ()
      | "int", Some e ->
          let expr_type = check_expr ctx e in
          if expr_type <> "int" then
            raise (SemanticError ("Return type mismatch: expected int, got " ^ expr_type))
          else ()
      | _ -> raise (SemanticError "Invalid return type in context"));
      ctx
      
  | Break | Continue ->
      if not ctx.in_loop then
        raise (SemanticError "'break' or 'continue' outside of a loop");
      ctx

let rec stmt_guarantees_return = function
  | Return _ -> true
  | If (_, then_s, Some else_s) -> stmt_guarantees_return then_s && stmt_guarantees_return else_s
  | Block stmts ->
      (match List.rev stmts with
      | [] -> false
      | last_stmt :: _ -> stmt_guarantees_return last_stmt)
  | _ -> false

let check_func_def func_table func =
  let initial_scope = StringMap.empty in
  let scope_with_params =
    List.fold_left (fun scope param_name ->
      if StringMap.mem param_name scope then
        raise (SemanticError ("Duplicate parameter name '" ^ param_name ^ "' in function '" ^ func.name ^ "'"));
      StringMap.add param_name "int" scope
    ) initial_scope func.params
  in

  let ctx = {
    func_table = func_table;
    var_scopes = [scope_with_params];
    current_func_ret_type = func.ret_type;
    in_loop = false;
  } in

  let _ = check_stmt ctx func.body in
  
  if func.ret_type = "int" && not (stmt_guarantees_return func.body) then
    raise (SemanticError ("Function '" ^ func.name ^ "' does not return a value on all control paths"));
  ()

(* --- 主分析函数 --- *)
let analyze comp_unit =
  let func_table =
    List.fold_left (fun table func ->
      if StringMap.mem func.name table then
        raise (SemanticError ("Function '" ^ func.name ^ "' is redefined"));
      let info = { f_ret_type = func.ret_type; f_param_names = func.params } in
      StringMap.add func.name info table
    ) StringMap.empty comp_unit
  in

  (match StringMap.find_opt "main" func_table with
  | None -> raise (SemanticError "Program entry point 'main' is not defined")
  | Some main_info ->
      if main_info.f_ret_type <> "int" then
        raise (SemanticError "'main' function must return int");
      if main_info.f_param_names <> [] then
        raise (SemanticError "'main' function must not have parameters"));

  List.iter (check_func_def func_table) comp_unit