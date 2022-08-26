open! Core

module Cmm = Ocamlc_kit.Cmm

module Dmm = Dmm_intf

module Dvar = Dmm.Dvar

module Node_id = Dmm.Node_id

module G = Graph.Imperative.Digraph.ConcreteBidirectional(Node_id)

type 'a t =
  { mutable current_node_id : Node_id.t 
  ; mutable current_var_id : int
  ; nodes : 'a Node_id.Table.t
  ; graph : G.t
  ; enter_id : Node_id.t
  ; exit_id : Node_id.t
  ; raise_id : Node_id.t
  ; temp_vars : Cmm.machtype Dvar.Table.t
  } [@@deriving fields]

let next_id (t : _ t) =
  let result = t.current_node_id in
  t.current_node_id <- Node_id.succ t.current_node_id;
  result

let insert t node_id value ~next =
  Hashtbl.add_exn t.nodes ~key:node_id ~data:value;
  G.add_vertex t.graph node_id;
  Array.iter next ~f:(G.add_edge t.graph node_id)

let temp t machtype =
  let var_id = t.current_var_id in
  t.current_var_id <- succ var_id;
  let v = Dvar.Temp var_id in
  Hashtbl.add_exn t.temp_vars ~key:v ~data:machtype;
  v

let map t ~f =
  let nodes = Hashtbl.map ~f t.nodes in
  { t with nodes }
