open ToyClib
open Ast
open Semantic
open Codegen

(* 修改parse_stdin支持Windows EOF *)
let parse_stdin () : comp_unit =
  let input = 
    let b = Buffer.create 16 in
    try while true do Buffer.add_string b (read_line () ^ "\n") done; ""
    with End_of_file -> Buffer.contents b 
  in
  let lexbuf = Lexing.from_string input in
  try 
    Parser.comp_unit Lexer.token lexbuf
  with
  | Lexer.LexError msg -> 
      Printf.eprintf "Lexer error at %d:%d: %s\n" 
        (lexbuf.lex_curr_p.pos_lnum) 
        (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol)
        msg;
      exit 1
  | Parsing.Parse_error ->
      Printf.eprintf "Parser error at %d:%d\n" 
        (lexbuf.lex_curr_p.pos_lnum)
        (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol);
      exit 1

(* 主逻辑函数 *)
let run_program () =
  let ast = parse_stdin () in
  (* 语义分析阶段 *)
  let _symbol_table = 
    try analyze ast
    with SemanticError msg ->
      Printf.eprintf "Semantic error: %s\n" msg;
      exit 1
  in
  (* 直接生成并输出汇编代码 *)
  let asm_code = compile ast in
  print_string asm_code;
  flush stdout

(* 移除所有输入提示 *)
let () = if not !Sys.interactive then run_program ()
