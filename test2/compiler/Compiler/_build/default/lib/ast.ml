(* AST definitions for ToyC language *)

(* 二元运算符 *)
type binop = 
  | Add | Sub | Mul | Div | Mod        (* 算术运算符 *)
  | Lt | Le | Gt | Ge | Eq | Ne        (* 关系运算符 *)
  | And | Or                           (* 逻辑运算符 *)

(* 一元运算符 *)
type unop = 
  | UPlus | UMinus | Not               (* +, -, ! *)

(* 表达式 *)
type expr = 
  | IntLit of int                      (* 整数字面量 *)
  | Var of string                      (* 变量引用 *)
  | BinOp of expr * binop * expr       (* 二元运算 *)
  | UnOp of unop * expr                (* 一元运算 *)
  | FuncCall of string * expr list     (* 函数调用 *)

(* 语句 *)
type stmt = 
  | Block of stmt list                 (* 语句块 *)
  | EmptyStmt                          (* 空语句 *)
  | ExprStmt of expr                   (* 表达式语句 *)
  | VarAssign of string * expr         (* 变量赋值 *)
  | VarDecl of string * expr           (* 变量声明 *)
  | If of expr * stmt * stmt option    (* if-else语句 *)
  | While of expr * stmt               (* while循环 *)
  | Break                              (* break语句 *)
  | Continue                           (* continue语句 *)
  | Return of expr option              (* return语句 *)

(* 函数参数 *)
type param = string                    (* 参数名 *)

(* 函数定义 *)
type func_def = {
  ret_type: string;                    (* 返回类型: "int" 或 "void" *)
  name: string;                        (* 函数名 *)
  params: param list;                  (* 参数列表 *)
  body: stmt;                          (* 函数体 *)
}

(* 编译单元 *)
type comp_unit = func_def list         (* 函数定义列表 *)

(* 辅助函数：打印AST *)
let string_of_binop = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"
  | Lt -> "<" | Le -> "<=" | Gt -> ">" | Ge -> ">=" | Eq -> "==" | Ne -> "!="
  | And -> "&&" | Or -> "||"

let string_of_unop = function
  | UPlus -> "+" | UMinus -> "-" | Not -> "!"

let rec string_of_expr = function
  | IntLit n -> string_of_int n
  | Var s -> s
  | BinOp (e1, op, e2) -> 
      "(" ^ string_of_expr e1 ^ " " ^ string_of_binop op ^ " " ^ string_of_expr e2 ^ ")"
  | UnOp (op, e) -> 
      "(" ^ string_of_unop op ^ string_of_expr e ^ ")"
  | FuncCall (name, args) ->
      name ^ "(" ^ String.concat ", " (List.map string_of_expr args) ^ ")"

let rec string_of_stmt_indent indent = function
  | Block stmts -> 
      "{\n" ^ String.concat "" (List.map (fun s -> 
        String.make (indent + 2) ' ' ^ string_of_stmt_indent (indent + 2) s ^ "\n") stmts) ^
      String.make indent ' ' ^ "}"
  | EmptyStmt -> ";"
  | ExprStmt e -> string_of_expr e ^ ";"
  | VarAssign (name, e) -> name ^ " = " ^ string_of_expr e ^ ";"
  | VarDecl (name, e) -> "int " ^ name ^ " = " ^ string_of_expr e ^ ";"
  | If (cond, then_stmt, else_stmt) ->
      "if (" ^ string_of_expr cond ^ ") " ^ string_of_stmt_indent indent then_stmt ^
      (match else_stmt with
       | Some s -> " else " ^ string_of_stmt_indent indent s
       | None -> "")
  | While (cond, body) ->
      "while (" ^ string_of_expr cond ^ ") " ^ string_of_stmt_indent indent body
  | Break -> "break;"
  | Continue -> "continue;"
  | Return (Some e) -> "return " ^ string_of_expr e ^ ";"
  | Return None -> "return;"

let string_of_stmt = string_of_stmt_indent 0

let string_of_func_def fd =
  fd.ret_type ^ " " ^ fd.name ^ "(" ^ 
  String.concat ", " (List.map (fun p -> "int " ^ p) fd.params) ^ ") " ^
  string_of_stmt fd.body

let string_of_comp_unit cu =
  String.concat "\n\n" (List.map string_of_func_def cu)