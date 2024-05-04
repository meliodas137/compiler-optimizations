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

(* function to find relevant move instruction in avail set *)
let find_move_in (avail: AvailSet.t) (y: operand): operand option= 
  let avail_list = AvailSet.elements avail in
  let rec helper (lst: Available.AvailSet.elt list) = (
    match lst with 
    | [] -> None
    | Move(z,c) :: _  when z=y -> Some(c)
    | _ :: tl -> helper tl)
  in
  helper avail_list   

(* function to get block from label *)
let block_from_label (b_label: string) (f: func): block = 
  let rec helper f = (
    match f with
      | [] -> raise Implement_Me
      | hd :: tl when ((find_block_label hd) = b_label) -> hd
      | _ :: tl -> helper tl 
  ) in
  helper f

(* function to perform cons copy propogation for a given instruction *)
let conscopy_prop_ins (i: inst) (f_acc: func) (b_acc: block) (b_label: string) (avail: AvailSet.t) (avail_map: avail_in_out) (pred_map: pred_map): (block * func * AvailSet.t) = 
  match i with 
    | Move(x, y) -> (
        match (find_move_in avail y) with
          | Some(c) -> (b_acc @ [Move(x, c)], f_acc, AvailSet.add (Move(x, c)) avail) 
          | None -> (b_acc @ [i], f_acc, AvailSet.add (Move(x, y)) avail) (* no cp *)
        )
    | Arith(x, y, op, z) -> (
      let updated_y = (
        match (find_move_in avail y) with
          | Some(c) -> c
          | None -> y (* no cp *)
        ) in
      let updated_z = (
        match (find_move_in avail z) with
          | Some(c) -> c
          | None -> z (* no cp *)
        ) in
      (b_acc @ [Arith(x, updated_y, op, updated_z)], f_acc, avail))
    | _ -> (b_acc @ [i], f_acc, avail)

(* function to perform cons copy prop for a given block *)
let conscopy_prop_block (b: block) (f_acc: func) (avail_map: avail_in_out) (pred_map: pred_map): func = 
  let block_label = find_block_label b in
  let (avail_in, _) = LabelMap.find block_label avail_map in (* initialize avail expression with avail in *)
  let rec helper (f_acc: func) (b_acc: block) (b_tail: block) (avail: AvailSet.t): (block * func * AvailSet.t) = (
    match b_tail with
      | [] -> (b_acc, (update_block b_acc f_acc), avail)
      | hd :: tl -> (
        let (b_acc, f_acc, avail) =  (conscopy_prop_ins hd f_acc b_acc block_label avail avail_map pred_map) in
        (helper f_acc b_acc tl avail)
      )
  ) in
  let (_, final_f, _) = (helper f_acc [] b avail_in) in
  (final_f)

(* driver to perform constant and copy propogation *)
let conscopy_prop (f : func) : func = 
  let avail_map = Available.available_expression f in
  let pred_map = Available.init_pred f in 
  (List.fold_left (fun f_acc b -> (conscopy_prop_block b f_acc avail_map pred_map)) f f)