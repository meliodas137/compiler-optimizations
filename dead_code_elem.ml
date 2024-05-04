open Liveness
open Cfg_ast
exception Implement_Me

let get_label (b: block) = match b with
 | (Label b)::_ -> b
 | _ -> raise Implement_Me


let op_to_inode = fun x -> match x with
  | Var(var) -> VarNode(var)
  | Reg(reg) -> RegNode(reg)
  | _ -> VarNode("NONE")

let dead_code inst l_set = match inst with 
  | Move(x, _)
  | Arith(x, _, _, _)
  | Load(x, _, _) -> (match x with 
      | Var(var) -> (match (NodeSet.find_opt (VarNode var) l_set) with None -> true | _ -> false)
      | Reg(reg) -> (match (NodeSet.find_opt (RegNode reg) l_set) with None -> true | _ -> false)
      | _ -> false
    )
  | _ -> false

let update_liveset inst live_set = 
  let (gen_list, kill_list) = get_gen_kill_inst inst in
  let l_set = List.fold_left (fun s x -> NodeSet.remove x s) live_set kill_list in
  List.fold_left (fun s x -> NodeSet.add x s) l_set gen_list 

let rec dead_code_block (b: block) (live_set) : block = match b with 
  | [] -> []
  | hd::tl -> if (dead_code hd live_set) 
    then dead_code_block tl live_set 
    else let l_set = update_liveset hd live_set in hd::(dead_code_block tl l_set)

let dead_code_elem (f: func) : func =
  let live_map = Liveness.build_liveness f in 
  let rec helper prog = (match prog with 
  | [] -> []
  | hd::tl -> let l = get_label hd in 
    let (_, lout) = StringMap.find l live_map in
    (List.rev (dead_code_block (List.rev (hd)) lout))::(helper tl)
  ) in helper f


