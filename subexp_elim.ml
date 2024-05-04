open Available
open Cfg_ast

exception Implement_Me

(* function to return avail in set for given block label *)
let get_avail_in b_label avail_map = (
  let (avail_in, _) = LabelMap.find b_label avail_map in
  avail_in
  )

(* function to return label of given block *)
let find_block_label (b:block): string = match b with Label(label)::_ -> label | _ -> raise Implement_Me

(* function to update given block in f *)
let update_block (b: block) (f: func): func = 
  let b_label = find_block_label b in
  let rec helper f_acc f_tail = (
    match f_tail with
      | [] -> raise Implement_Me
      | hd :: tl when ((find_block_label hd) = b_label) -> f_acc @ [b] @ tl
      | hd :: tl -> helper (f_acc @ [hd]) tl 
  ) in
  helper [] f

(* function to extract binary exp from instruction *)
let get_bop_exp (i: inst): aexp option = 
  match i with 
    | Arith(_, x, op, y) -> Some(B_op(x, op, y))
    | _ -> None

(* function to get block from label *)
let block_from_label (b_label: string) (f: func): block = 
  let rec helper f = (
    match f with
      | [] -> raise Implement_Me
      | hd :: tl when ((find_block_label hd) = b_label) -> hd
      | _ :: tl -> helper tl 
  ) in
  helper f

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
let rec traverse_pred_tree (b_label: string) (e: aexp) (f_acc:func) (temp:string) (avail_map: avail_in_out) (pred_map: pred_map): func = 
  let pred_list = LabelSet.to_list (get_pred_set b_label pred_map) in
  let rec helper (b_label: string) (f_acc:func) : func = (
    match (traverse_block e (block_from_label b_label f_acc) temp (get_avail_in b_label avail_map)) with
      | Some(b_updated) -> (update_block b_updated f_acc)
      | None -> (traverse_pred_tree b_label e f_acc temp avail_map pred_map)
  ) in
  (List.fold_left (fun f_acc pred -> (helper pred f_acc)) f_acc pred_list)

(* function to perform CSE for a given instruction *)
let subexp_elim_ins (i: inst) (f_acc: func) (b_acc: block) (b_label: string) (avail: AvailSet.t) (avail_map: avail_in_out) (pred_map: pred_map): (block * func * AvailSet.t) = 
  let exp = get_bop_exp i in
  let b_avail_in = get_avail_in b_label avail_map in
  match exp with 
    | None -> (b_acc @ [i], f_acc, avail) (* ins not eligible for cse as it's not bop *)
    | Some(e) -> 
      if (AvailSet.mem e avail) (* exp available *)
      then (
        let temp = new_temp() in (* temp variable to use in cse *)
        match (traverse_block e b_acc temp b_avail_in) with
          None -> (
              match i with 
                  | Arith(x, _, _, _) -> (b_acc @ [Move(x, Var(temp))], (traverse_pred_tree b_label e f_acc temp avail_map pred_map), AvailSet.add e avail)
                  | _ -> raise Implement_Me
          )
          | Some(b_acc_updated) -> (* available exp found in curr block *) 
              match i with 
                | Arith(x, _, _, _) -> (b_acc_updated @ [Move(x, Var(temp))], f_acc, AvailSet.add e avail)
                | _ -> raise Implement_Me
      )
      else (b_acc @ [i], f_acc, AvailSet.add e avail) (* exp not available *)

(* function to perform CSE for a given block *)
let subexp_elim_block (b: block) (f_acc: func) (avail_map: avail_in_out) (pred_map: pred_map): func = 
  let block_label = find_block_label b in
  let (avail_in, _) = LabelMap.find block_label avail_map in (* initialize avail expression with avail in *)
  let rec helper (f_acc: func) (b_acc: block) (b_tail: block) (avail: AvailSet.t): (block * func * AvailSet.t) = (
    match b_tail with
      | [] -> (b_acc, (update_block b_acc f_acc), avail)
      | hd :: tl -> (
        let (b_acc, f_acc, avail) =  (subexp_elim_ins hd f_acc b_acc block_label avail avail_map pred_map) in
        (helper f_acc b_acc tl avail)
      )
  ) in
  let (_, final_f, _) = (helper f_acc [] b avail_in) in
  (final_f)

(* driver to perform common subexpression elimination *)
let subexp_elim (f : func) : func = 
  let avail_map = Available.available_expression f in
  let pred_map = Available.init_pred f in 
  (List.fold_left (fun f_acc b -> (subexp_elim_block b f_acc avail_map pred_map)) f f) (* TODO: update sequence of blocks to dfs *)