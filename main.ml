open Cish_ast
open Cfg_ast

(* This magic is used to glue the generated lexer and parser together.
 * Expect one command-line argument, a file to parse.
 * You do not need to understand this interaction with the system. *)
let parse_file() =
  let argv = Sys.argv in
  let _ = 
    if Array.length argv != 2
    then (prerr_string ("usage: " ^ argv.(0) ^ " [file-to-parse]\n");
    exit 1) in
  let ch = open_in argv.(1) in
  Cish_parse.program Cish_lex.lexer (Lexing.from_channel ch)

let parse_stdin() = 
  Cish_parse.program Cish_lex.lexer (Lexing.from_channel stdin)

let process_fn fn =
  let curfblocks = (Cfg_ast.fn2blocks fn) in
  (match fn with
   | Fn {name; args; body; pos} -> print_string ("==========================\nProcessing function: " ^ name ^ "\n"));
  print_string ("blocks =\n" ^
    (Cfg_ast.fun2string curfblocks)^ "\n");
  let ae = Available.available_expression curfblocks in
  let opt_blocks_se = Subexp_elim.subexp_elim curfblocks in
  let opt_blocks_cp = Conscopy_prop.conscopy_prop opt_blocks_se in
  let opt_blocks_dc = Dead_code_elem.dead_code_elem opt_blocks_cp in
  (print_string ("available expressions =\n" ^
  (Available.string_of_avails ae)^ "\n");
  print_string ("blocks after common subexp elimination =\n" ^
  (Cfg_ast.fun2string opt_blocks_se)^ "\n");
  print_string ("blocks after constant and copy propogation =\n" ^
  (Cfg_ast.fun2string opt_blocks_cp)^ "\n");
  print_string ("blocks after dead code elimination =\n" ^
  (Cfg_ast.fun2string opt_blocks_dc)^ "\n");
  )
  
  


let _ =
  let prog = parse_file() in
  List.iter (fun fn -> process_fn fn) prog
