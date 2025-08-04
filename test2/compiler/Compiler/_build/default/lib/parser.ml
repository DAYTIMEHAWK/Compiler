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
# 14 "lib/parser.ml"
)
  | NUMBER of (
# 10 "lib/parser.mly"
        int
# 19 "lib/parser.ml"
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

open Parsing
let _ = parse_error;;
# 4 "lib/parser.mly"
open Ast
# 48 "lib/parser.ml"
let yytransl_const = [|
  257 (* INT *);
  258 (* VOID *);
  259 (* IF *);
  260 (* ELSE *);
  261 (* WHILE *);
  262 (* BREAK *);
  263 (* CONTINUE *);
  264 (* RETURN *);
  267 (* PLUS *);
  268 (* MINUS *);
  269 (* TIMES *);
  270 (* DIV *);
  271 (* MOD *);
  272 (* EQ *);
  273 (* NEQ *);
  274 (* LT *);
  275 (* LE *);
  276 (* GT *);
  277 (* GE *);
  278 (* AND *);
  279 (* OR *);
  280 (* NOT *);
  281 (* ASSIGN *);
  282 (* LPAREN *);
  283 (* RPAREN *);
  284 (* LBRACE *);
  285 (* RBRACE *);
  286 (* SEMICOLON *);
  287 (* COMMA *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  265 (* ID *);
  266 (* NUMBER *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\003\000\003\000\003\000\003\000\004\000\
\004\000\006\000\005\000\005\000\007\000\007\000\008\000\008\000\
\008\000\008\000\008\000\008\000\008\000\008\000\008\000\008\000\
\008\000\008\000\009\000\010\000\010\000\011\000\011\000\012\000\
\012\000\012\000\012\000\012\000\012\000\012\000\013\000\013\000\
\013\000\014\000\014\000\014\000\014\000\015\000\015\000\015\000\
\015\000\016\000\016\000\016\000\016\000\016\000\017\000\017\000\
\000\000"

let yylen = "\002\000\
\002\000\001\000\002\000\006\000\006\000\005\000\005\000\001\000\
\003\000\002\000\003\000\002\000\001\000\002\000\001\000\001\000\
\002\000\004\000\005\000\005\000\007\000\005\000\002\000\002\000\
\002\000\003\000\001\000\001\000\003\000\001\000\003\000\001\000\
\003\000\003\000\003\000\003\000\003\000\003\000\001\000\003\000\
\003\000\001\000\003\000\003\000\003\000\001\000\002\000\002\000\
\002\000\001\000\001\000\003\000\004\000\003\000\001\000\003\000\
\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\057\000\000\000\000\000\000\000\
\000\000\001\000\003\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\010\000\000\000\006\000\000\000\000\000\
\007\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\051\000\000\000\000\000\000\000\000\000\012\000\016\000\
\015\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\042\000\046\000\004\000\009\000\005\000\000\000\000\000\
\000\000\023\000\024\000\000\000\025\000\000\000\000\000\000\000\
\047\000\048\000\049\000\000\000\011\000\014\000\017\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\026\000\
\000\000\054\000\000\000\000\000\052\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\043\000\
\044\000\045\000\000\000\000\000\000\000\018\000\000\000\053\000\
\019\000\000\000\022\000\056\000\000\000\021\000"

let yydgoto = "\002\000\
\005\000\006\000\007\000\016\000\041\000\017\000\042\000\043\000\
\044\000\045\000\046\000\047\000\048\000\049\000\050\000\051\000\
\092\000"

let yysindex = "\004\000\
\050\255\000\000\254\254\000\255\000\000\013\000\050\255\253\254\
\010\255\000\000\000\000\003\255\007\255\031\255\014\255\029\255\
\013\255\014\255\040\255\000\000\009\255\000\000\014\255\057\255\
\000\000\014\255\066\255\071\255\074\255\077\255\081\255\017\255\
\051\255\000\000\062\255\062\255\062\255\062\255\000\000\000\000\
\000\000\052\255\084\255\083\255\107\255\114\255\072\000\093\255\
\055\255\000\000\000\000\000\000\000\000\000\000\120\255\062\255\
\062\255\000\000\000\000\127\255\000\000\116\255\062\255\191\255\
\000\000\000\000\000\000\135\255\000\000\000\000\000\000\062\255\
\062\255\062\255\062\255\062\255\062\255\062\255\062\255\062\255\
\062\255\062\255\062\255\062\255\062\255\136\255\137\255\000\000\
\117\255\000\000\139\255\152\255\000\000\114\255\072\000\093\255\
\093\255\093\255\093\255\093\255\093\255\055\255\055\255\000\000\
\000\000\000\000\150\255\084\255\084\255\000\000\062\255\000\000\
\000\000\177\255\000\000\000\000\084\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\183\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\157\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\176\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\178\255\000\000\072\255\054\000\182\255\203\255\
\121\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\104\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\181\255\000\000\000\000\056\000\045\000\219\255\
\235\255\251\255\011\000\027\000\043\000\138\255\155\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\054\255\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\203\000\000\000\254\255\083\000\000\000\168\000\193\255\
\224\255\000\000\142\000\143\000\020\001\048\000\222\255\000\000\
\116\000"

let yytablesize = 355
let yytable = "\062\000\
\065\000\066\000\067\000\014\000\001\000\068\000\008\000\014\000\
\009\000\027\000\019\000\028\000\010\000\029\000\030\000\031\000\
\032\000\033\000\034\000\035\000\036\000\053\000\012\000\086\000\
\087\000\060\000\034\000\035\000\036\000\015\000\089\000\091\000\
\037\000\018\000\038\000\013\000\021\000\039\000\040\000\020\000\
\037\000\021\000\038\000\024\000\114\000\115\000\061\000\104\000\
\105\000\106\000\003\000\004\000\107\000\118\000\020\000\023\000\
\020\000\014\000\020\000\020\000\020\000\020\000\020\000\020\000\
\020\000\020\000\026\000\082\000\083\000\084\000\060\000\034\000\
\035\000\036\000\055\000\063\000\064\000\020\000\091\000\020\000\
\069\000\020\000\020\000\020\000\027\000\037\000\028\000\038\000\
\029\000\030\000\031\000\032\000\033\000\034\000\035\000\036\000\
\056\000\022\000\027\000\057\000\025\000\027\000\027\000\080\000\
\081\000\052\000\058\000\037\000\054\000\038\000\059\000\021\000\
\071\000\040\000\050\000\050\000\050\000\050\000\050\000\050\000\
\050\000\050\000\050\000\050\000\050\000\050\000\050\000\102\000\
\103\000\072\000\050\000\039\000\039\000\050\000\050\000\073\000\
\039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
\085\000\088\000\110\000\039\000\040\000\040\000\039\000\039\000\
\064\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
\040\000\093\000\108\000\109\000\040\000\041\000\041\000\040\000\
\040\000\111\000\041\000\041\000\041\000\041\000\041\000\041\000\
\041\000\041\000\112\000\113\000\117\000\041\000\002\000\008\000\
\041\000\041\000\050\000\050\000\050\000\050\000\050\000\050\000\
\050\000\050\000\050\000\050\000\050\000\050\000\050\000\060\000\
\034\000\035\000\036\000\030\000\030\000\050\000\013\000\055\000\
\030\000\011\000\070\000\030\000\030\000\094\000\037\000\095\000\
\038\000\090\000\032\000\032\000\032\000\032\000\032\000\032\000\
\032\000\032\000\116\000\000\000\000\000\032\000\000\000\000\000\
\032\000\032\000\037\000\037\000\037\000\037\000\037\000\037\000\
\037\000\037\000\000\000\000\000\000\000\037\000\000\000\000\000\
\037\000\037\000\038\000\038\000\038\000\038\000\038\000\038\000\
\038\000\038\000\000\000\000\000\000\000\038\000\000\000\000\000\
\038\000\038\000\033\000\033\000\033\000\033\000\033\000\033\000\
\033\000\033\000\000\000\000\000\000\000\033\000\000\000\000\000\
\033\000\033\000\034\000\034\000\034\000\034\000\034\000\034\000\
\034\000\034\000\000\000\000\000\000\000\034\000\000\000\000\000\
\034\000\034\000\035\000\035\000\035\000\035\000\035\000\035\000\
\035\000\035\000\000\000\000\000\000\000\035\000\000\000\000\000\
\035\000\035\000\036\000\036\000\036\000\036\000\036\000\036\000\
\036\000\036\000\031\000\031\000\000\000\036\000\000\000\031\000\
\036\000\036\000\031\000\031\000\028\000\000\000\029\000\000\000\
\028\000\000\000\029\000\028\000\028\000\029\000\029\000\074\000\
\075\000\076\000\077\000\078\000\079\000\096\000\097\000\098\000\
\099\000\100\000\101\000"

let yycheck = "\032\000\
\035\000\036\000\037\000\001\001\001\000\038\000\009\001\001\001\
\009\001\001\001\013\000\003\001\000\000\005\001\006\001\007\001\
\008\001\009\001\010\001\011\001\012\001\024\000\026\001\056\000\
\057\000\009\001\010\001\011\001\012\001\027\001\063\000\064\000\
\024\001\027\001\026\001\026\001\028\001\029\001\030\001\009\001\
\024\001\028\001\026\001\031\001\108\000\109\000\030\001\082\000\
\083\000\084\000\001\001\002\001\085\000\117\000\001\001\027\001\
\003\001\001\001\005\001\006\001\007\001\008\001\009\001\010\001\
\011\001\012\001\027\001\013\001\014\001\015\001\009\001\010\001\
\011\001\012\001\009\001\025\001\026\001\024\001\111\000\026\001\
\029\001\028\001\029\001\030\001\001\001\024\001\003\001\026\001\
\005\001\006\001\007\001\008\001\009\001\010\001\011\001\012\001\
\026\001\015\000\027\001\026\001\018\000\030\001\031\001\011\001\
\012\001\023\000\030\001\024\001\026\000\026\001\030\001\028\001\
\030\001\030\001\011\001\012\001\013\001\014\001\015\001\016\001\
\017\001\018\001\019\001\020\001\021\001\022\001\023\001\080\000\
\081\000\023\001\027\001\011\001\012\001\030\001\031\001\022\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\025\001\030\001\030\001\027\001\011\001\012\001\030\001\031\001\
\026\001\016\001\017\001\018\001\019\001\020\001\021\001\022\001\
\023\001\027\001\027\001\027\001\027\001\011\001\012\001\030\001\
\031\001\031\001\016\001\017\001\018\001\019\001\020\001\021\001\
\022\001\023\001\027\001\030\001\004\001\027\001\000\000\027\001\
\030\001\031\001\011\001\012\001\013\001\014\001\015\001\016\001\
\017\001\018\001\019\001\020\001\021\001\022\001\023\001\009\001\
\010\001\011\001\012\001\022\001\023\001\030\001\029\001\027\001\
\027\001\007\000\043\000\030\001\031\001\072\000\024\001\073\000\
\026\001\027\001\016\001\017\001\018\001\019\001\020\001\021\001\
\022\001\023\001\111\000\255\255\255\255\027\001\255\255\255\255\
\030\001\031\001\016\001\017\001\018\001\019\001\020\001\021\001\
\022\001\023\001\255\255\255\255\255\255\027\001\255\255\255\255\
\030\001\031\001\016\001\017\001\018\001\019\001\020\001\021\001\
\022\001\023\001\255\255\255\255\255\255\027\001\255\255\255\255\
\030\001\031\001\016\001\017\001\018\001\019\001\020\001\021\001\
\022\001\023\001\255\255\255\255\255\255\027\001\255\255\255\255\
\030\001\031\001\016\001\017\001\018\001\019\001\020\001\021\001\
\022\001\023\001\255\255\255\255\255\255\027\001\255\255\255\255\
\030\001\031\001\016\001\017\001\018\001\019\001\020\001\021\001\
\022\001\023\001\255\255\255\255\255\255\027\001\255\255\255\255\
\030\001\031\001\016\001\017\001\018\001\019\001\020\001\021\001\
\022\001\023\001\022\001\023\001\255\255\027\001\255\255\027\001\
\030\001\031\001\030\001\031\001\023\001\255\255\023\001\255\255\
\027\001\255\255\027\001\030\001\031\001\030\001\031\001\016\001\
\017\001\018\001\019\001\020\001\021\001\074\000\075\000\076\000\
\077\000\078\000\079\000"

let yynames_const = "\
  INT\000\
  VOID\000\
  IF\000\
  ELSE\000\
  WHILE\000\
  BREAK\000\
  CONTINUE\000\
  RETURN\000\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIV\000\
  MOD\000\
  EQ\000\
  NEQ\000\
  LT\000\
  LE\000\
  GT\000\
  GE\000\
  AND\000\
  OR\000\
  NOT\000\
  ASSIGN\000\
  LPAREN\000\
  RPAREN\000\
  LBRACE\000\
  RBRACE\000\
  SEMICOLON\000\
  COMMA\000\
  EOF\000\
  "

let yynames_block = "\
  ID\000\
  NUMBER\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'func_def_list) in
    Obj.repr(
# 36 "lib/parser.mly"
                      ( _1 )
# 308 "lib/parser.ml"
               : Ast.comp_unit))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'func_def) in
    Obj.repr(
# 39 "lib/parser.mly"
             ( [_1] )
# 315 "lib/parser.ml"
               : 'func_def_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'func_def) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'func_def_list) in
    Obj.repr(
# 40 "lib/parser.mly"
                           ( _1 :: _2 )
# 323 "lib/parser.ml"
               : 'func_def_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'param_list) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 44 "lib/parser.mly"
                                          (
      { ret_type = "int"; name = _2; params = _4; body = _6 }
    )
# 334 "lib/parser.ml"
               : 'func_def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'param_list) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 47 "lib/parser.mly"
                                           (
      { ret_type = "void"; name = _2; params = _4; body = _6 }
    )
# 345 "lib/parser.ml"
               : 'func_def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 50 "lib/parser.mly"
                               (
      { ret_type = "int"; name = _2; params = []; body = _5 }
    )
# 355 "lib/parser.ml"
               : 'func_def))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 53 "lib/parser.mly"
                                (
      { ret_type = "void"; name = _2; params = []; body = _5 }
    )
# 365 "lib/parser.ml"
               : 'func_def))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'param) in
    Obj.repr(
# 59 "lib/parser.mly"
          ( [_1] )
# 372 "lib/parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'param) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'param_list) in
    Obj.repr(
# 60 "lib/parser.mly"
                           ( _1 :: _3 )
# 380 "lib/parser.ml"
               : 'param_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 63 "lib/parser.mly"
           ( _2 )
# 387 "lib/parser.ml"
               : 'param))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'stmt_list) in
    Obj.repr(
# 67 "lib/parser.mly"
                            ( Block _2 )
# 394 "lib/parser.ml"
               : 'block))
; (fun __caml_parser_env ->
    Obj.repr(
# 68 "lib/parser.mly"
                  ( Block [] )
# 400 "lib/parser.ml"
               : 'block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 71 "lib/parser.mly"
         ( [_1] )
# 407 "lib/parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'stmt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'stmt_list) in
    Obj.repr(
# 72 "lib/parser.mly"
                   ( _1 :: _2 )
# 415 "lib/parser.ml"
               : 'stmt_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 76 "lib/parser.mly"
          ( _1 )
# 422 "lib/parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 77 "lib/parser.mly"
              ( EmptyStmt )
# 428 "lib/parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 78 "lib/parser.mly"
                   ( ExprStmt _1 )
# 435 "lib/parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 79 "lib/parser.mly"
                             ( VarAssign (_1, _3) )
# 443 "lib/parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 80 "lib/parser.mly"
                                 ( VarDecl (_2, _4) )
# 451 "lib/parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 81 "lib/parser.mly"
                               ( If (_3, _5, None) )
# 459 "lib/parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'stmt) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 82 "lib/parser.mly"
                                         ( If (_3, _5, Some _7) )
# 468 "lib/parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'stmt) in
    Obj.repr(
# 83 "lib/parser.mly"
                                  ( While (_3, _5) )
# 476 "lib/parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 84 "lib/parser.mly"
                    ( Break )
# 482 "lib/parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 85 "lib/parser.mly"
                       ( Continue )
# 488 "lib/parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 86 "lib/parser.mly"
                     ( Return None )
# 494 "lib/parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 87 "lib/parser.mly"
                          ( Return (Some _2) )
# 501 "lib/parser.ml"
               : 'stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'lor_expr) in
    Obj.repr(
# 91 "lib/parser.mly"
             ( _1 )
# 508 "lib/parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'land_expr) in
    Obj.repr(
# 95 "lib/parser.mly"
              ( _1 )
# 515 "lib/parser.ml"
               : 'lor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'lor_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'land_expr) in
    Obj.repr(
# 96 "lib/parser.mly"
                          ( BinOp (_1, Or, _3) )
# 523 "lib/parser.ml"
               : 'lor_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'rel_expr) in
    Obj.repr(
# 100 "lib/parser.mly"
             ( _1 )
# 530 "lib/parser.ml"
               : 'land_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'land_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'rel_expr) in
    Obj.repr(
# 101 "lib/parser.mly"
                           ( BinOp (_1, And, _3) )
# 538 "lib/parser.ml"
               : 'land_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'add_expr) in
    Obj.repr(
# 105 "lib/parser.mly"
             ( _1 )
# 545 "lib/parser.ml"
               : 'rel_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'rel_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'add_expr) in
    Obj.repr(
# 106 "lib/parser.mly"
                         ( BinOp (_1, Lt, _3) )
# 553 "lib/parser.ml"
               : 'rel_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'rel_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'add_expr) in
    Obj.repr(
# 107 "lib/parser.mly"
                         ( BinOp (_1, Le, _3) )
# 561 "lib/parser.ml"
               : 'rel_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'rel_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'add_expr) in
    Obj.repr(
# 108 "lib/parser.mly"
                         ( BinOp (_1, Gt, _3) )
# 569 "lib/parser.ml"
               : 'rel_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'rel_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'add_expr) in
    Obj.repr(
# 109 "lib/parser.mly"
                         ( BinOp (_1, Ge, _3) )
# 577 "lib/parser.ml"
               : 'rel_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'rel_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'add_expr) in
    Obj.repr(
# 110 "lib/parser.mly"
                         ( BinOp (_1, Eq, _3) )
# 585 "lib/parser.ml"
               : 'rel_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'rel_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'add_expr) in
    Obj.repr(
# 111 "lib/parser.mly"
                          ( BinOp (_1, Ne, _3) )
# 593 "lib/parser.ml"
               : 'rel_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'mul_expr) in
    Obj.repr(
# 115 "lib/parser.mly"
             ( _1 )
# 600 "lib/parser.ml"
               : 'add_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'add_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'mul_expr) in
    Obj.repr(
# 116 "lib/parser.mly"
                           ( BinOp (_1, Add, _3) )
# 608 "lib/parser.ml"
               : 'add_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'add_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'mul_expr) in
    Obj.repr(
# 117 "lib/parser.mly"
                            ( BinOp (_1, Sub, _3) )
# 616 "lib/parser.ml"
               : 'add_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'unary_expr) in
    Obj.repr(
# 121 "lib/parser.mly"
               ( _1 )
# 623 "lib/parser.ml"
               : 'mul_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'mul_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'unary_expr) in
    Obj.repr(
# 122 "lib/parser.mly"
                              ( BinOp (_1, Mul, _3) )
# 631 "lib/parser.ml"
               : 'mul_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'mul_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'unary_expr) in
    Obj.repr(
# 123 "lib/parser.mly"
                            ( BinOp (_1, Div, _3) )
# 639 "lib/parser.ml"
               : 'mul_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'mul_expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'unary_expr) in
    Obj.repr(
# 124 "lib/parser.mly"
                            ( BinOp (_1, Mod, _3) )
# 647 "lib/parser.ml"
               : 'mul_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'primary_expr) in
    Obj.repr(
# 128 "lib/parser.mly"
                 ( _1 )
# 654 "lib/parser.ml"
               : 'unary_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'unary_expr) in
    Obj.repr(
# 129 "lib/parser.mly"
                                ( UnOp (UPlus, _2) )
# 661 "lib/parser.ml"
               : 'unary_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'unary_expr) in
    Obj.repr(
# 130 "lib/parser.mly"
                                  ( UnOp (UMinus, _2) )
# 668 "lib/parser.ml"
               : 'unary_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'unary_expr) in
    Obj.repr(
# 131 "lib/parser.mly"
                   ( UnOp (Not, _2) )
# 675 "lib/parser.ml"
               : 'unary_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 135 "lib/parser.mly"
       ( Var _1 )
# 682 "lib/parser.ml"
               : 'primary_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 136 "lib/parser.mly"
           ( IntLit _1 )
# 689 "lib/parser.ml"
               : 'primary_expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 137 "lib/parser.mly"
                       ( _2 )
# 696 "lib/parser.ml"
               : 'primary_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr_list) in
    Obj.repr(
# 138 "lib/parser.mly"
                               ( FuncCall (_1, _3) )
# 704 "lib/parser.ml"
               : 'primary_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    Obj.repr(
# 139 "lib/parser.mly"
                     ( FuncCall (_1, []) )
# 711 "lib/parser.ml"
               : 'primary_expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 143 "lib/parser.mly"
         ( [_1] )
# 718 "lib/parser.ml"
               : 'expr_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr_list) in
    Obj.repr(
# 144 "lib/parser.mly"
                         ( _1 :: _3 )
# 726 "lib/parser.ml"
               : 'expr_list))
(* Entry comp_unit *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let comp_unit (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.comp_unit)
;;
