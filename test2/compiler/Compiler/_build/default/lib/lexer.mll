{
  open Parser 
  exception LexError of string
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let ident = (alpha | '_') (alpha | digit | '_')*
let integer = '0' | ['1'-'9'] digit*

rule token = parse
  (* 空白字符 *)
  | [' ' '\t' '\r' '\n'] { token lexbuf }
  
  (* 注释 *)
  | "//" [^ '\n']* '\n' { token lexbuf }
  | "/*" ([^ '*'] | '*' [^ '/'])* "*/" { token lexbuf }

  (* 关键字 *)
  | "int"     { INT }
  | "void"    { VOID }
  | "if"      { IF }
  | "else"    { ELSE }
  | "while"   { WHILE }
  | "break"   { BREAK }
  | "continue" { CONTINUE }
  | "return"  { RETURN }
  
  (* 标识符 *)
  | ident as id { ID id }
  
  (* 整数常量 *)
  | integer as num { NUMBER (int_of_string num) }
  
  (* 运算符 *)
  | "=="    { EQ }
  | "!="    { NEQ }
  | "<="    { LE }
  | ">="    { GE }
  | "&&"    { AND }
  | "||"    { OR }
  | '+'     { PLUS }
  | '-'     { MINUS }
  | '*'     { TIMES }
  | '/'     { DIV }
  | '%'     { MOD }
  | '!'     { NOT }
  | '<'     { LT }
  | '>'     { GT }
  | '='     { ASSIGN }
  
  (* 分隔符 *)
  | '('     { LPAREN }
  | ')'     { RPAREN }
  | '{'     { LBRACE }
  | '}'     { RBRACE }
  | ';'     { SEMICOLON }
  | ','     { COMMA }
  
  (* 文件结束 *)
  | eof     { EOF }
  
  (* 错误处理 *)
  | _ as c  { raise (LexError ("Illegal character: " ^ String.make 1 c)) }