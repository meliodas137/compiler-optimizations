open Available
open Cfg_ast

exception Implement_Me

(* function to return label of given block *)
let find_block_label (b:block): string = raise Implement_Me

(* function to update given block in f *)
let update_block (b: block) (f: func): func = raise Implement_Me

(* function to perform CSE for a given instruction *)
let subexp_elim_ins (i: inst) (f_acc: func) (b_acc: block) (avail: AvailSet.t): (block * func * AvailSet.t) = 
  raise Implement_Me

(* function to perform CSE for a given block *)
let subexp_elim_block (b: block) (f_acc: func) (avail_map: avail_in_out): func = 
  let block_label = find_block_label b in
  let (block_avail, _) = LabelMap.find block_label avail_map in (* initialize avail expression with avail in *)
  let rec helper (f_acc: func) (b_acc: block) (b_tail: block) (avail: AvailSet.t): (block * func * AvailSet.t) = (
    match b_tail with
      | [] -> (b_acc, (update_block b_acc f_acc), avail)
      | hd :: tl -> (
        let (b_acc, f_acc, avail) =  (subexp_elim_ins hd f_acc b_acc avail) in
        (helper f_acc b_acc tl avail)
      )
  ) in
  let (_, final_f, _) = (helper f_acc [] b block_avail) in
  (final_f)

(* driver to perform common subexpression elimination *)
let subexp_elim (f : func) : func = 
  let avail_map = Available.available_expression f in
  let rec helper (f_acc : func) (f_tail : func) : func = (
    match f_tail with
      | [] -> f_acc
      | hd :: tl -> helper (subexp_elim_block hd f_acc avail_map) tl  
  ) in
  (helper f f)