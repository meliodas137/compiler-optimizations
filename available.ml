open Cfg_ast
exception Implement_Me
exception FatalError

type aexp = B_op of (operand * arithop * operand) | Mem of (operand*int)
module AExpression =
struct
  type t = aexp
  let compare = compare
end

module LabelMap = Map.Make(String)

module AvailSet = Set.Make(AExpression)

module LabelSet = Set.Make(String)

type in_out = ((AvailSet.t * AvailSet.t) LabelMap.t)

type pred_map = (LabelSet.t LabelMap.t)

(* kill and gen functions for available expressions *)
let contain_var (x: operand) (inst: aexp) : bool = match x with
  | Int _ | Lab _ -> false
  | Reg _ | Var _ as op -> (
    match inst with
    | B_op (op1, a_op, op2) -> if op1 == op || op2 == op then true else false
    | Mem (op1, _) -> if op1 == op then true else false
  )

let prune (x: operand) (r_set: AvailSet.t) : AvailSet.t = AvailSet.filter (fun inst -> not (contain_var x inst)) r_set

let rec inst_gen_helper (inst: inst) (r_set: AvailSet.t) = match inst with 
  | Arith (s, op2, a_op, op3) -> prune s (AvailSet.add (B_op (op2, a_op, op3)) r_set)
  | Load(s, op2, i) -> prune s (AvailSet.add (Mem (op2, i)) r_set)
  | _ -> r_set
and
inst_kill_helper (inst: inst) (r_set: AvailSet.t) = match inst with 
  | Arith (t, _, _, _) -> AvailSet.filter (fun inst -> contain_var t inst) r_set
  | Load(t, _, _) -> AvailSet.filter (fun inst -> contain_var t inst) r_set
  | Store(_, _, _) | Call _-> AvailSet.filter (fun inst -> match inst with Mem _ -> true | _ -> false) r_set
  | _ -> r_set
(* End of kill and gen *)


(* Initializing the available map; in_set = {}, out_set = {All possible exp} *)
let collect_all_exp inst r_set = match inst with 
  | Arith (op1, op2, a_op, op3) -> AvailSet.add (B_op (op2, a_op, op3)) r_set
  | Load(op1, op2, i) -> AvailSet.add (Mem (op2, i)) r_set
  | _ -> r_set

let rec init_avail_helper (b: block) (reach_map: in_out): in_out = match b with
  | (Label l)::tl -> let out_set = List.fold_left (fun acc x -> collect_all_exp x acc) AvailSet.empty b in
    LabelMap.add l (AvailSet.empty, out_set) reach_map
  | _ -> reach_map

let rec init_avail (f: func): in_out = 
  List.fold_left (fun acc x -> init_avail_helper x acc) LabelMap.empty f
(* End of init *)

(* Construct Pred mapping to use further *)
let get_pred_set l map = (match LabelMap.find_opt l map with None -> LabelSet.empty | Some s -> s)

let update_pred inst acc pred_l = match inst with 
  | Jump l -> LabelMap.add l (LabelSet.add pred_l (get_pred_set l acc)) acc
  | If(_, _, _, l1, l2) -> 
    let new_acc = LabelMap.add l2 (LabelSet.add pred_l (get_pred_set l2 acc)) acc in 
    LabelMap.add l1 (LabelSet.add pred_l (get_pred_set l1 new_acc)) new_acc
  | _ -> acc

let init_pred (f: func) : pred_map = 
  let init_pred_helper (pm: pred_map) (b: block) : pred_map = (match b with 
    | (Label l)::_ -> List.fold_left (fun acc inst -> update_pred inst acc l) pm b
    | _ -> pm) in
  List.fold_left (fun acc x -> init_pred_helper acc x) LabelMap.empty f
(* End of pred map construction *)

(* Main available expression loop *)
let map_compare (tup1: (AvailSet.t * AvailSet.t)) (tup2: (AvailSet.t* AvailSet.t)) =
  if ((AvailSet.equal (fst tup1) (fst tup2)) && (AvailSet.equal (snd tup1) (snd tup2))) then true else false

let get_avail_out_set l mp = 
  let (_, out) = (match LabelMap.find_opt l mp with None -> (AvailSet.empty, AvailSet.empty) | Some s -> s)
  in out

let rec construct_in (old_am: in_out) (pred_list: String.t list) : AvailSet.t = match pred_list with
  | [] -> AvailSet.empty 
  | hd::[] -> get_avail_out_set hd old_am
  | hd::tl -> AvailSet.inter (get_avail_out_set hd old_am) (construct_in old_am tl)
  
let rec construct_out (b: block) (old_am: in_out) (new_in: AvailSet.t) : AvailSet.t =
  let gen = List.fold_left (fun acc inst -> inst_gen_helper inst acc) AvailSet.empty b in
  let kill = List.fold_left (fun acc inst -> inst_kill_helper inst acc) AvailSet.empty b in
  (AvailSet.union gen (AvailSet.diff new_in kill))

let rec available_dataflow_helper (b: block) (new_am: in_out) (old_am: in_out) (pm: pred_map): in_out = match b with 
  | (Label l)::_ -> 
    let new_in = construct_in old_am (LabelSet.to_list (get_pred_set l pm)) in 
    let new_out = construct_out b old_am new_in in
    LabelMap.add l (new_in, new_out) new_am
  | _ -> new_am

let rec construct_available_dataflow (f: func) (old_am: in_out) (pm: pred_map): in_out = 
  let new_am = List.fold_left (fun acc b -> available_dataflow_helper b acc old_am pm) LabelMap.empty f in 
  if (LabelMap.equal map_compare new_am old_am) then new_am else construct_available_dataflow f new_am pm
(* End of main loop *)

(* Driver Function *)
let rec available_expression (f : func) : in_out = 
  let am = init_avail f in 
  let pm = init_pred f in
  construct_available_dataflow f am pm
(* End of Driver*)

(******************************** Printing Functions **********************************)

let print_set (s: AvailSet.t) = 
  let aexp_to_string aexp = match aexp with 
  | B_op (op1, a_op, op2) -> (op2string op1) ^ (arithop2string a_op) ^ (op2string op2)
  | Mem (op, i) -> "*(" ^ (op2string op) ^ "+" ^ (string_of_int i)^")" in
  let exp_strings = List.map aexp_to_string (AvailSet.to_list s) in
  String.concat "; " exp_strings

let string_of_avails (ae: in_out) : string = 
  let print_label_exp (k, (v_in, v_out)) = Printf.sprintf "%s:\n\tin: %s\n\tout:%s" k (print_set v_in) (print_set v_out) in
  let rows = String.concat "\n" (List.map print_label_exp (LabelMap.to_list ae)) in 
  Printf.sprintf "{\n%s\n}" rows
