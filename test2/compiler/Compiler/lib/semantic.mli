(* semantic.mli *)

open Ast

exception SemanticError of string

(* 
  对给定的AST进行语义分析。
  如果发现语义错误，会抛出 SemanticError 异常。
  如果成功，则不返回任何内容。
*)
val analyze : comp_unit -> unit