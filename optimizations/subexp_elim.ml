open Available
open Cfg_ast

exception Implement_Me

(* function to return label of given block *)
let find_block_label (b:block): string = raise Implement_Me

(* function to update given block in f *)
let update_block (b: block) (f: func): func = raise Implement_Me

(* function to extract binary exp from instruction *)
let get_bop_exp (i: inst): aexp option = raise Implement_Me

(* function to find the available exp by traversing a block in reverse
   returns: None if exp not found in block
            Some of updated block if exp found *)
let traverse_block (e: aexp) (b: block) (temp: string) (avail_in: AvailSet.t): block option = 
  if (AvailSet.mem e avail_in) then None (* exp in avail_in means it is not present in b *)
  else (
    let b_rev = List.rev b in
    let rec helper (b_acc: block) (b_tail: block): block = (
      match b_tail with
        | [] -> b_acc
        | hd :: tl -> 
            match (get_bop_exp hd) with
              | Some(e1) when e1 = e -> (
                  match hd with 
                    | Arith(x, y, op, z) when x <> Var(temp) -> (b_acc @ [Move(x, Var(temp)); Arith(Var(temp), y, op, z)] @ tl)
                    | Arith(x, y, op, z) -> (b_acc @ [hd] @ tl)
                    | _ -> raise Implement_Me
              )
              | _ -> helper (b_acc @ [hd]) (tl) 
    ) in
    Some(List.rev (helper [] b_rev))
  )

(* function to find availabe exp in the predecessor tree of given label *)
let traverse_pred_tree (b_label: string) (e: aexp) (f_acc:func) (temp:string): func = raise Implement_Me 

(* function to perform CSE for a given instruction *)
let subexp_elim_ins (i: inst) (f_acc: func) (b_acc: block) (b_label: string) (avail: AvailSet.t) (b_avail_in: AvailSet.t): (block * func * AvailSet.t) = 
  let exp = get_bop_exp i in
  match exp with 
    | None -> (b_acc @ [i], f_acc, avail) (* ins not eligible for cse as it's not bop *)
    | Some(e) -> 
      if (AvailSet.mem e avail) (* exp available *)
      then (
        let temp = new_temp() in (* temp variable to use in cse *)
        match (traverse_block e b_acc temp b_avail_in) with
          None -> (
              match i with 
                  | Arith(x, _, _, _) -> (b_acc @ [Move(x, Var(temp))], (traverse_pred_tree b_label e f_acc temp), AvailSet.add e avail)
                  | _ -> raise Implement_Me
          )
          | Some(b_acc_updated) -> (* available exp found in curr block *) 
              match i with 
                | Arith(x, _, _, _) -> (b_acc_updated @ [Move(x, Var(temp))], f_acc, AvailSet.add e avail)
                | _ -> raise Implement_Me
      )
      else (b_acc @ [i], f_acc, AvailSet.add e avail) (* exp not available *)

(* function to perform CSE for a given block *)
let subexp_elim_block (b: block) (f_acc: func) (avail_map: avail_in_out): func = 
  let block_label = find_block_label b in
  let (avail_in, _) = LabelMap.find block_label avail_map in (* initialize avail expression with avail in *)
  let rec helper (f_acc: func) (b_acc: block) (b_tail: block) (avail: AvailSet.t): (block * func * AvailSet.t) = (
    match b_tail with
      | [] -> (b_acc, (update_block b_acc f_acc), avail)
      | hd :: tl -> (
        let (b_acc, f_acc, avail) =  (subexp_elim_ins hd f_acc b_acc block_label avail avail_in) in
        (helper f_acc b_acc tl avail)
      )
  ) in
  let (_, final_f, _) = (helper f_acc [] b avail_in) in
  (final_f)

(* driver to perform common subexpression elimination *)
let subexp_elim (f : func) : func = 
  let avail_map = Available.available_expression f in
  let rec helper (f_acc : func) (f_tail : func) : func = (
    match f_tail with
      | [] -> f_acc
      | hd :: tl -> helper (subexp_elim_block hd f_acc avail_map) tl  (* TODO: update sequence of blocks to dfs *)
  ) in
  (helper f f)