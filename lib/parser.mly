/* Parser for ToyC language */

%{
open Ast
%}

/* Token declarations */
%token INT VOID IF ELSE WHILE BREAK CONTINUE RETURN
%token <string> ID
%token <int> NUMBER
%token PLUS MINUS TIMES DIV MOD
%token EQ NEQ LT LE GT GE
%token AND OR NOT
%token ASSIGN
%token LPAREN RPAREN LBRACE RBRACE SEMICOLON COMMA
%token EOF

/* Precedence and associativity */
%left OR
%left AND
%left EQ NEQ
%left LT LE GT GE
%left PLUS MINUS
%left TIMES DIV MOD
%right NOT UMINUS UPLUS
%nonassoc ELSE

/* Start symbol */
%start comp_unit
%type <Ast.comp_unit> comp_unit

%%

/* 编译单元 */
comp_unit:
  | func_def_list EOF { $1 }

func_def_list:
  | func_def { [$1] }
  | func_def func_def_list { $1 :: $2 }

/* 函数定义 */
func_def:
  | INT ID LPAREN param_list RPAREN block {
      { ret_type = "int"; name = $2; params = $4; body = $6 }
    }
  | VOID ID LPAREN param_list RPAREN block {
      { ret_type = "void"; name = $2; params = $4; body = $6 }
    }
  | INT ID LPAREN RPAREN block {
      { ret_type = "int"; name = $2; params = []; body = $5 }
    }
  | VOID ID LPAREN RPAREN block {
      { ret_type = "void"; name = $2; params = []; body = $5 }
    }

/* 参数列表 */
param_list:
  | param { [$1] }
  | param COMMA param_list { $1 :: $3 }

param:
  | INT ID { $2 }

/* 语句块 */
block:
  | LBRACE stmt_list RBRACE { Block $2 }
  | LBRACE RBRACE { Block [] }

stmt_list:
  | stmt { [$1] }
  | stmt stmt_list { $1 :: $2 }

/* 语句 */
stmt:
  | block { $1 }
  | SEMICOLON { EmptyStmt }
  | expr SEMICOLON { ExprStmt $1 }
  | ID ASSIGN expr SEMICOLON { VarAssign ($1, $3) }
  | INT ID ASSIGN expr SEMICOLON { VarDecl ($2, $4) }
  | IF LPAREN expr RPAREN stmt { If ($3, $5, None) }
  | IF LPAREN expr RPAREN stmt ELSE stmt { If ($3, $5, Some $7) }
  | WHILE LPAREN expr RPAREN stmt { While ($3, $5) }
  | BREAK SEMICOLON { Break }
  | CONTINUE SEMICOLON { Continue }
  | RETURN SEMICOLON { Return None }
  | RETURN expr SEMICOLON { Return (Some $2) }

/* 表达式 */
expr:
  | lor_expr { $1 }

/* 逻辑或表达式 */
lor_expr:
  | land_expr { $1 }
  | lor_expr OR land_expr { BinOp ($1, Or, $3) }

/* 逻辑与表达式 */
land_expr:
  | rel_expr { $1 }
  | land_expr AND rel_expr { BinOp ($1, And, $3) }

/* 关系表达式 */
rel_expr:
  | add_expr { $1 }
  | rel_expr LT add_expr { BinOp ($1, Lt, $3) }
  | rel_expr LE add_expr { BinOp ($1, Le, $3) }
  | rel_expr GT add_expr { BinOp ($1, Gt, $3) }
  | rel_expr GE add_expr { BinOp ($1, Ge, $3) }
  | rel_expr EQ add_expr { BinOp ($1, Eq, $3) }
  | rel_expr NEQ add_expr { BinOp ($1, Ne, $3) }

/* 加减表达式 */
add_expr:
  | mul_expr { $1 }
  | add_expr PLUS mul_expr { BinOp ($1, Add, $3) }
  | add_expr MINUS mul_expr { BinOp ($1, Sub, $3) }

/* 乘除模表达式 */
mul_expr:
  | unary_expr { $1 }
  | mul_expr TIMES unary_expr { BinOp ($1, Mul, $3) }
  | mul_expr DIV unary_expr { BinOp ($1, Div, $3) }
  | mul_expr MOD unary_expr { BinOp ($1, Mod, $3) }

/* 一元表达式 */
unary_expr:
  | primary_expr { $1 }
  | PLUS unary_expr %prec UPLUS { UnOp (UPlus, $2) }
  | MINUS unary_expr %prec UMINUS { UnOp (UMinus, $2) }
  | NOT unary_expr { UnOp (Not, $2) }

/* 基本表达式 */
primary_expr:
  | ID { Var $1 }
  | NUMBER { IntLit $1 }
  | LPAREN expr RPAREN { $2 }
  | ID LPAREN expr_list RPAREN { FuncCall ($1, $3) }
  | ID LPAREN RPAREN { FuncCall ($1, []) }

/* 表达式列表 */
expr_list:
  | expr { [$1] }
  | expr COMMA expr_list { $1 :: $3 }

%%