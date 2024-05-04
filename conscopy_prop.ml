open Available
open Cfg_ast

exception Implement_Me


(* driver to perform constant propogation *)
let conscopy_prop (f : func) : func = 
  f