open Available
open Cfg_ast

exception Implement_Me
(* function to perform CSE for a given block *)
let subexp_elim_block (b: block) (f_acc: func) (avail_map: avail_in_out): func = raise Implement_Me


(* driver to perform common subexpression elimination *)
let subexp_elim (f : func) : func = 
  let avail_map = Available.available_expression f in
  let rec subexp_elim_helper (f_acc : func) (f_tail : func) : func = (
    match f_tail with
      | [] -> f_acc
      | hd :: tl -> subexp_elim_helper (subexp_elim_block hd f_acc avail_map) tl  
  ) in
  (subexp_elim_helper f f)