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
(* These are the registers that must be generated / killed as part of
   liveness analysis for call instructions to reflect MIPS calling
   conventions *)


let call_gen_list = ["$4";"$5";"$6";"$7"]
let call_kill_list = ["$1";"$2";"$3";"$4";"$5";"$6";"$7";"$8";"$9";"$10";
                      "$11";"$12";"$13";"$14";"$15";"$24";"$25";"$31"]
(* Undirected graphs where nodes are identified by igraph_node type above. Look at
   graph.ml for the interface description.  *)

module IUGraph = Graph.UndirectedGraph(IGraphNode)

(* this is a wrapper to addEdge that prevents adding self edges.
   to do all sorts of other complicated stuff for eg coloring *)
let specialAddEdge u v g =
  if (u = v) then
    g
  else
    IUGraph.addEdge u v g

(* An interference graph is an SUGraph where a node is temp variable
   or a register (to be able to handle pre-colored nodes)

   The adjacency set of variable x should be the set of variables
   y such that x and y are live at the same point in time. *)
type interfere_graph = IUGraph.graph

(* To help you printing an igraph for debugging *)
let string_of_igraph (g: interfere_graph) : string =
  let rec string_of_row (n: IUGraph.node) =
    let ns = IUGraph.adj n g in
    Printf.sprintf "%s : {%s}"
      (string_of_node n)
      (String.concat "," (List.map string_of_node (NodeSet.elements ns)))
  in
  let rows = String.concat "\n" (List.map string_of_row (NodeSet.elements (IUGraph.nodes g))) in
  Printf.sprintf "{\n%s\n}" rows
  

(*******************************************************************)
(* PS7 TODO:  interference graph construction *)

(* given a function (i.e., list of basic blocks), construct the
 * interference graph for that function.  This will require that
 * you build a dataflow analysis for calculating what set of variables
 * are live-in and live-out for each program point. *)

(* module LabelMap = Map.Make(String)

module LiveSet = Set.Make(String)
let changed = ref false
let step = ref 0
let in_map = ref LabelMap.empty
let out_map = ref LabelMap.empty
let old_in_map = ref LabelMap.empty
let old_out_map = ref LabelMap.empty
let rec succ (l: block) : string list = match l with
| [] -> [] 
| (Jump l)::tl -> l::(succ tl)
| (If(_, _, _, l1, l2))::tl -> l1::l2::(succ tl)
| _::tl -> succ tl

let neq_has x set = (match (LiveSet.find_opt x set) with None -> true | _ -> false)

let rec gen_l (op_list) (g_set: LiveSet.t) (k_set: LiveSet.t): LiveSet.t = match op_list with
  | [] -> g_set 
  | (Var x)::tl -> if neq_has x k_set then (gen_l tl (LiveSet.add x g_set)) k_set else gen_l tl g_set k_set
  | (Reg r)::tl -> if neq_has (Mips.reg2string r) k_set then (gen_l tl (LiveSet.add (Mips.reg2string r) g_set)) k_set else gen_l tl g_set k_set
  | (Lab x)::tl -> if neq_has x k_set then (gen_l tl (LiveSet.add x g_set)) k_set else gen_l tl g_set k_set
  | _::tl -> gen_l tl g_set k_set

let rec kill_l (op_list) (k_set: LiveSet.t) : LiveSet.t =  match op_list with
  | [] -> k_set 
  | (Var x)::tl -> (kill_l tl (LiveSet.add x k_set))
  | (Reg r)::tl -> (kill_l tl (LiveSet.add (Mips.reg2string r) k_set))
  | (Lab x)::tl -> (kill_l tl (LiveSet.add x k_set))
  | _::tl -> kill_l tl k_set

let toVar (op: operand) : string = match op with
  | (Var x) -> x
  | (Reg r) -> Mips.reg2string r
  | (Lab x) -> x
  | _ -> ""

let inst_gen_kill l_set gen_list kill_list = 
  let plusGen = (List.fold_left (fun set x -> LiveSet.add (toVar x) set) l_set gen_list) in
  let minusKill = (List.fold_left (fun set x -> LiveSet.remove (toVar x) set) plusGen kill_list) in
  LiveSet.remove "" minusKill

let rec g_k_union (out: LiveSet.t) (b: block) (g_set: LiveSet.t) (k_set: LiveSet.t): LiveSet.t = match b with
  | [] -> LiveSet.union g_set (LiveSet.diff out k_set)
  | hd::tl -> let helper inst g_set k_set do_kill: LiveSet.t = ( 
    match inst with 
    | Label _ | Jump _ -> if do_kill then k_set else g_set
    | Move(op1, op2) | Load(op1, op2, _) -> if do_kill then kill_l [op1] k_set else gen_l [op2] g_set k_set
    | Arith (op1, op2, a_op, op3) -> if do_kill then kill_l [op1] k_set else gen_l [op2; op3]  g_set k_set
    | Store(op1, x, op2) -> if do_kill then k_set else gen_l [op2] g_set k_set
    | Call op -> if do_kill 
      then kill_l (List.map (fun x -> Var x) call_kill_list) k_set 
      else gen_l (op::(List.map (fun x -> Var x) call_gen_list)) g_set k_set
    | If(op1, comp_op, op2, l1, l2) -> if do_kill then k_set else gen_l [op1; op2] g_set k_set
    | Return -> if do_kill then k_set else gen_l [Reg Mips.R2] g_set k_set
    ) in g_k_union out tl (helper hd g_set k_set false) (helper hd g_set k_set true)

let g_in out block : LiveSet.t = (g_k_union out block LiveSet.empty LiveSet.empty)

let union_helper (l: block) : LiveSet.t = 
  List.fold_left (fun acc x -> LiveSet.union acc x) (LiveSet.empty) 
  (List.map (fun li -> LabelMap.find li !old_in_map) (succ l))
  
let rec construct_reachable_dataflow (f : func) = 
  if !step <> 0 && not (!changed)  
  then ()
  else (
    step := 1;
    changed := false;
    old_in_map := !in_map;
    old_out_map := !out_map;
    let rec loop_helper (f: func) = match f with
      | [] -> ()
      | (((Label label)::ttl) as l1)::tl -> 
        let out = (union_helper l1) in
        if LiveSet.equal out (LabelMap.find label !old_out_map) 
        then loop_helper tl 
        else (
          changed := true;
          out_map := LabelMap.add label out !old_out_map; 
          in_map := LabelMap.add label (g_in out l1) !old_in_map; 
          loop_helper tl
        )
      | _ -> () in let _ = loop_helper f in
      construct_reachable_dataflow f
    )
    
let makeNode x = match x with 
  "$0" -> RegNode Mips.R0 | "$1" -> RegNode Mips.R1 | "$2" -> RegNode Mips.R2 | "$3" -> RegNode Mips.R3 | "$4" -> RegNode Mips.R4 |
  "$5" -> RegNode Mips.R5 | "$6" -> RegNode Mips.R6 | "$7" -> RegNode Mips.R7 | "$8" -> RegNode Mips.R8 | "$9" -> RegNode Mips.R9 |
  "$10" -> RegNode Mips.R10 | "$11" -> RegNode Mips.R11 | "$12" -> RegNode Mips.R12 | "$13" -> RegNode Mips.R13
  | "$14" -> RegNode Mips.R14 | "$15" -> RegNode Mips.R15 | "$16" -> RegNode Mips.R16 
  | "$17" -> RegNode Mips.R17 | "$18" -> RegNode Mips.R18 | "$19" -> RegNode Mips.R19 | "$20" -> RegNode Mips.R20
  | "$21" -> RegNode Mips.R21 | "$22" -> RegNode Mips.R22 | "$23" -> RegNode Mips.R23 | "$24" -> RegNode Mips.R24
  | "$25" -> RegNode Mips.R25 | "$26" -> RegNode Mips.R26 | "$27" -> RegNode Mips.R27 | "$28" -> RegNode Mips.R28
  | "$29" -> RegNode Mips.R29 | "$30" -> RegNode Mips.R30 | "$31" -> RegNode Mips.R31 | _ -> VarNode x
  
let addNodeAndEdge (g: interfere_graph) (n: igraph_node) (m: igraph_node): interfere_graph = 
  let g1 = IUGraph.addNode m (IUGraph.addNode n g) in (IUGraph.addEdge n m g1)

let rec add_edges (g: interfere_graph) (l_list: string list) : interfere_graph = match l_list with
  | [] -> g
  | hd::tl -> let rec add_edges_helper g from too = match too with
    | [] -> g 
    | hdd::tll -> add_edges_helper (addNodeAndEdge g (makeNode from) (makeNode hdd)) from tll
     in (add_edges (add_edges_helper g hd tl) tl)
  
let updated_graph (b: block) (gr: interfere_graph) : interfere_graph = match b with
  | [] -> gr
  | (Label l)::tll -> 
    let l_out = (LabelMap.find l !out_map) in
    let rec updated_graph_helper (b:block) (g: interfere_graph) (l_set: LiveSet.t): interfere_graph = ( 
      match b with 
      | [] -> g
      | (Label _)::tl -> updated_graph_helper tl g l_set
      | (Move(op1, op2))::tl -> let n_l_in = inst_gen_kill l_set [op2] [op1] in 
      updated_graph_helper tl (add_edges g (LiveSet.to_list n_l_in)) n_l_in
      | (Arith (op1, op2, a_op, op3))::tl -> let n_l_in = inst_gen_kill l_set [op2; op3] [op1] in 
      updated_graph_helper tl (add_edges g (LiveSet.to_list n_l_in)) n_l_in
      | (Load(op1, op2, x))::tl -> let n_l_in = inst_gen_kill l_set [op2] [op1] in 
      updated_graph_helper tl (add_edges g (LiveSet.to_list n_l_in)) n_l_in
      | (Store(op1, x, op2))::tl -> let n_l_in = inst_gen_kill l_set [op2] [] in 
      updated_graph_helper tl (add_edges g (LiveSet.to_list n_l_in)) n_l_in
      | (Call op)::tl -> let n_l_in = inst_gen_kill l_set (op::(List.map (fun x -> Var x) call_gen_list)) (List.map (fun x -> Var x) call_kill_list) in 
      updated_graph_helper tl (add_edges g (LiveSet.to_list n_l_in)) n_l_in
      | (Jump label)::tl -> updated_graph_helper tl g l_set
      | (If(op1, comp_op, op2, l1, l2))::tl -> 
        let n_l_in = inst_gen_kill l_set [op1; op2] [] in 
      updated_graph_helper tl (add_edges g (LiveSet.to_list n_l_in)) n_l_in
      | (Return)::tl -> let n_l_in = inst_gen_kill l_set [Reg Mips.R2] [] in 
      updated_graph_helper tl (add_edges g (LiveSet.to_list n_l_in)) n_l_in
    ) in 
    updated_graph_helper (List.rev tll) gr l_out
  | _ -> gr

let rec init_in_out_map (f: func) = match f with 
  | [] -> true
  | (((Label l)::_) as b)::tl -> 
    let ls = (g_in LiveSet.empty b) in
    in_map := LabelMap.add l ls !in_map;
    old_in_map := LabelMap.add l ls !old_in_map;
    old_out_map := LabelMap.add l (LiveSet.empty) !old_out_map;
    out_map := LabelMap.add l (LiveSet.empty) !out_map;
    init_in_out_map tl
  | _::tl -> init_in_out_map tl

let rec build_interfere_graph (f : func) : interfere_graph = 
  in_map := LabelMap.empty;
  out_map := LabelMap.empty;
  old_in_map := LabelMap.empty;
  old_out_map := LabelMap.empty;
  step := 0;
  changed := false;
  let _ = init_in_out_map f in 
  let _ = construct_reachable_dataflow f in 
  let rec graph_helper f g = (match f with
  | [] -> g
  | block::tl -> graph_helper tl (updated_graph block g)
  ) in graph_helper f IUGraph.empty *)
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

(* Main available expression loop *)
let map_compare (tup1: (AvailSet.t * AvailSet.t)) (tup2: (AvailSet.t* AvailSet.t)) =
  if ((AvailSet.equal (fst tup1) (fst tup2)) && (AvailSet.equal (snd tup1) (snd tup2))) then true else false

let rec available_dataflow_helper (f: func) (am: in_out) (pm: pred_map): in_out = raise Implement_Me

let rec construct_available_dataflow (f: func) (old_am: in_out) (pm: pred_map): in_out = 
  let new_am = available_dataflow_helper f old_am pm in 
  if (LabelMap.equal map_compare new_am old_am) then new_am else construct_available_dataflow f new_am pm
(* End of main loop *)

(* Construct Pred mapping to use further *)
let get_set l map = (match LabelMap.find_opt l map with None -> LabelSet.empty | Some s -> s)

let update_pred inst acc pred_l = match inst with 
  | Jump l -> LabelMap.add l (LabelSet.add pred_l (get_set l acc)) acc
  | If(_, _, _, l1, l2) -> 
    let new_acc = LabelMap.add l2 (LabelSet.add pred_l (get_set l2 acc)) acc in 
    LabelMap.add l1 (LabelSet.add pred_l (get_set l1 new_acc)) new_acc
  | _ -> acc

let init_pred (f: func) : pred_map = 
  let init_pred_helper (pm: pred_map) (b: block) : pred_map = (match b with 
    | (Label l)::_ -> List.fold_left (fun acc inst -> update_pred inst acc l) pm b
    | _ -> pm) in
  List.fold_left (fun acc x -> init_pred_helper acc x) LabelMap.empty f
(* End of pred map construction *)

(* Driver Function *)
let rec build_interfere_graph (f : func) : in_out = 
  let am = init_avail f in 
  let pm = init_pred f in
  construct_available_dataflow f am pm