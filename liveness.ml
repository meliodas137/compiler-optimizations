open Cfg_ast
exception Implement_Me
exception FatalError


type igraph_node = RegNode of Mips.reg | VarNode of var

let string_of_node (n: igraph_node) : string =
  match n with
  | RegNode r -> Mips.reg2string r
  | VarNode v -> v
;;

module IGraphNode =
  struct
    type t = igraph_node
    let compare = compare
  end

module NodeSet = Set.Make(IGraphNode)      
module StringMap = Map.Make(String)                                             
(* These are the registers that must be generated / killed as part of
   liveness analysis for call instructions to reflect MIPS calling
   conventions *)

let call_gen_list = ["$4";"$5";"$6";"$7"]
let call_kill_list = ["$1";"$2";"$3";"$4";"$5";"$6";"$7";"$8";"$9";"$10";
                      "$11";"$12";"$13";"$14";"$15";"$24";"$25";"$31"]

type liout_map = (NodeSet.t * NodeSet.t) StringMap.t
 
let rec oplst_to_igraphlst op_list acc = 
  match op_list with 
    | [] -> acc
    | Var(var)::tl -> oplst_to_igraphlst tl (VarNode(var)::acc)
    | Reg(reg)::tl -> oplst_to_igraphlst tl (RegNode(reg)::acc)
    | _::tl -> oplst_to_igraphlst tl acc

let get_gen_kill_inst (i: inst) = 
  match i with
      Label(_) -> ([], [])
    | Move(op1, op2) -> (oplst_to_igraphlst [op2] [], oplst_to_igraphlst [op1] [])
    | Arith(op1, op2, arith, op3) -> (oplst_to_igraphlst [op2; op3] [], oplst_to_igraphlst [op1] [])
    | Load(op1, op2, _) -> (oplst_to_igraphlst [op2] [], oplst_to_igraphlst [op1] [])
    | Store(_, _, op2) -> (oplst_to_igraphlst [op2] [], [])
    | Call(op1) -> ([RegNode(Mips.R4); RegNode(Mips.R5); RegNode(Mips.R6); RegNode(Mips.R7)],
                    [RegNode(Mips.R1); RegNode(Mips.R2); RegNode(Mips.R3); RegNode(Mips.R4);
                    RegNode(Mips.R8); RegNode(Mips.R5); RegNode(Mips.R6); RegNode(Mips.R7);
                    RegNode(Mips.R9); RegNode(Mips.R10); RegNode(Mips.R11); RegNode(Mips.R12);
                    RegNode(Mips.R13); RegNode(Mips.R14); RegNode(Mips.R15);
                    RegNode(Mips.R24); RegNode(Mips.R25); RegNode(Mips.R31);])
    | Jump(label) -> ([], [])
    | If(op1, compop, op2, label1, label2) -> (oplst_to_igraphlst [op1; op2] [], [])
    | Return -> ([RegNode(Mips.R2)], [])

let map_compare tup1 tup2 =
  if ((NodeSet.equal (fst tup1) (fst tup2)) && (NodeSet.equal (snd tup1) (snd tup2))) then true else false

let rec generate_blocks_genkill (f : func) (kmap, gmap) = 
  match f with
  [] -> (kmap, gmap)
  | hd :: tl -> (
    let l_label = match hd with Label(label)::_ -> label | _ -> print_string "error in generate_blocks_genkill"; raise FatalError in
    let rec generate_inst_genkill (kill_set) (gen_set) (b: block) = (
      match b with
      [] -> (kill_set, gen_set)
      | ihd :: itl -> (
        let (gen_list, kill_list) = get_gen_kill_inst ihd in
        let rec process_gens gen_list (gen_set) = (
          match gen_list with
            [] -> gen_set
            | ghd :: gtl -> process_gens gtl (if (NodeSet.mem ghd kill_set) then gen_set else (NodeSet.add ghd gen_set))
        ) in
        let rec process_kills kill_list (kill_set) = (
          match kill_list with
            [] -> kill_set
            | khd :: ktl -> process_kills ktl (NodeSet.add khd kill_set)
        ) in
        let kill_set_updt = process_kills kill_list kill_set in
        let gen_set_updt = process_gens gen_list gen_set in
        (generate_inst_genkill kill_set_updt gen_set_updt itl)
      )
    ) in
    let (kill_set, gen_set) = (generate_inst_genkill NodeSet.empty NodeSet.empty hd) in
    let kmap = StringMap.add l_label kill_set kmap in
    let gmap = StringMap.add l_label gen_set gmap in
    (generate_blocks_genkill tl (kmap, gmap))

  )

let rec initialize_lin_lout (genl_map) (f : func) (lio_map: liout_map): liout_map = 
  match f with
  [] -> lio_map
  | hd :: tl -> (
    let l_label = match hd with Label(label)::_ -> label | _ -> print_string "error in initialize_lin_lout"; raise FatalError in
    (initialize_lin_lout genl_map tl (StringMap.add l_label ((StringMap.find l_label genl_map), NodeSet.empty) lio_map))
  )

let rec find_succ_of_block (b: block) = 
  match List.rev b with
    [] -> []
    | Jump(label) :: _ -> [label]
    | If(_, _, _, label1, label2) :: _ -> [label1; label2]
    | Return :: _ -> []
    | _ -> print_string "error in find_succ_of_block"; raise FatalError

let build_liveness (f : func) = 
  let (killl_map, genl_map) = generate_blocks_genkill f (StringMap.empty, StringMap.empty) in
  let lin_lout_map = (initialize_lin_lout genl_map f StringMap.empty) in
  let find_succ_lin_union l_label map = (
    let rec helper f = (
      match f with
        [] -> print_string "error1 in find_succ_lin_union"; raise FatalError
        | hd :: tl -> (
          let hd_label = match hd with Label(label)::_ -> label | _ -> print_string "error2 in find_succ_lin_union"; raise FatalError in
          if (hd_label = l_label) then ((List.fold_left (fun set elem -> NodeSet.union set (fst (StringMap.find elem map)))) (NodeSet.empty) (find_succ_of_block hd))
          else (helper tl)
          )
          
    ) in (helper f)     
  ) in
  let rec update_lin_lout_map f map = (
    match f with
      [] -> map
      | hd :: tl -> (
        let l_label = match hd with Label(label)::_ -> label | _ -> print_string "error in update_lin_lout_map";raise FatalError in
        let out = find_succ_lin_union l_label map in
        (if (NodeSet.equal out (snd (StringMap.find l_label map))) 
          then (update_lin_lout_map tl map)
          else (
            let lout = out in
            let lin = NodeSet.union (StringMap.find l_label genl_map) (NodeSet.diff lout (StringMap.find l_label killl_map)) in
            update_lin_lout_map tl (StringMap.add l_label (lin, lout) map))
        ) 
      )
  ) in
  let rec loop_until_no_change old_map new_map = (
    if (StringMap.equal map_compare old_map new_map) then new_map 
    else (loop_until_no_change new_map (update_lin_lout_map f new_map))
  ) in
  loop_until_no_change lin_lout_map (update_lin_lout_map f lin_lout_map) 
