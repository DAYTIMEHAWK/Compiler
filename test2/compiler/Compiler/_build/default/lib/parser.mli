type token =
  | INT
  | VOID
  | IF
  | ELSE
  | WHILE
  | BREAK
  | CONTINUE
  | RETURN
  | ID of (
# 9 "lib/parser.mly"
        string
# 14 "lib/parser.mli"
)
  | NUMBER of (
# 10 "lib/parser.mly"
        int
# 19 "lib/parser.mli"
)
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | MOD
  | EQ
  | NEQ
  | LT
  | LE
  | GT
  | GE
  | AND
  | OR
  | NOT
  | ASSIGN
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | SEMICOLON
  | COMMA
  | EOF

val comp_unit :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.comp_unit
