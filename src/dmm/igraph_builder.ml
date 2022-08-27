open! Core

module Cmm = Ocamlc_kit.Cmm

module Dmm = Dmm_intf

module Dvar = Dmm.Dvar

module Node_id = Dmm.Node_id

module Edge_ordering = struct
  type t = int [@@deriving compare]
  let default = 0
end

module G = Graph.Imperative.Digraph.ConcreteBidirectionalLabeled(Node_id)(Edge_ordering)

type 'a t =
  { mutable current_node_id : Node_id.t 
  ; mutable current_var_id : int
  ; nodes : 'a Node_id.Table.t
  ; graph : (G.t [@sexp.opaque])
  ; enter_id : Node_id.t
  ; exit_id : Node_id.t
  ; raise_id : Node_id.t
  ; temp_vars : Cmm.machtype Dvar.Table.t
  } [@@deriving fields]

let next_g graph node_id =
  G.succ_e graph node_id
  |> List.sort ~compare:[%compare: _ * int * Node_id.t]
  |> List.map ~f:Tuple3.get3

let sexp_of_t
    sexp_of_a
    { current_node_id
    ; current_var_id
    ; nodes
    ; graph
    ; enter_id
    ; exit_id
    ; raise_id
    ; temp_vars
    }
  =
  let module Top = Graph.Topological.Make(G) in
  let graph =
    Top.fold
      (fun node_id acc ->
         if Node_id.equal node_id exit_id
         || Node_id.equal node_id raise_id
         then acc
         else begin
           let c = Hashtbl.find_exn nodes node_id in
           let next = next_g graph node_id in
           [%sexp
             { node_id : Node_id.t
             ; next : Node_id.t list
             ; c : a 
             }] :: acc
         end
      )
      graph
      []
  in
  let graph = List.rev graph in
  [%sexp
    { current_node_id : Node_id.t 
    ; current_var_id : int
    ; enter_id : Node_id.t
    ; exit_id : Node_id.t
    ; raise_id : Node_id.t
    ; temp_vars : Cmm.machtype Dvar.Table.t
    ; graph : Sexp.t list
    }]

let to_dot { nodes; exit_id; raise_id; graph; _ } ~f =
  let b = Buffer.create 1000 in
  Buffer.add_string b "digraph igraph {\n";
  Hashtbl.iteri nodes
    ~f:(fun ~key ~data:contents ->
        Printf.sprintf "%i [ label = \"%s\"];\n" (Node_id.to_int key) (f contents)
        |> Buffer.add_string b;
        let next = next_g graph key in
        List.iter next
          ~f:(fun next ->
              Printf.sprintf "%i -> %i;\n" (Node_id.to_int key) (Node_id.to_int next)
              |> Buffer.add_string b
            )
      )
  ;
  Buffer.add_string b (Printf.sprintf "%i [ label = \"<EXIT>\"]\n"  (Node_id.to_int exit_id));
  Buffer.add_string b (Printf.sprintf "%i [ label = \"<RAISE>\"]\n"  (Node_id.to_int raise_id));
  Buffer.add_string b "}\n";
  Buffer.contents b

let next_id (t : _ t) =
  let result = t.current_node_id in
  t.current_node_id <- Node_id.succ t.current_node_id;
  result

let insert t node_id value ~next =
  Hashtbl.add_exn t.nodes ~key:node_id ~data:value;
  G.add_vertex t.graph node_id;
  Array.iteri next
    ~f:(fun i v -> G.add_edge_e t.graph (G.E.create node_id i v))

let temp t machtype =
  let var_id = t.current_var_id in
  t.current_var_id <- succ var_id;
  let v = Dvar.Temp var_id in
  Hashtbl.add_exn t.temp_vars ~key:v ~data:machtype;
  v

let map t ~f =
  let nodes = Hashtbl.map ~f t.nodes in
  let temp_vars = Hashtbl.copy t.temp_vars in
  let graph = G.copy t.graph in
  { t with nodes; temp_vars; graph }

let create
  ()
  =
  let exit_id = Node_id.zero in
  let raise_id = Node_id.succ exit_id in
  let enter_id = Node_id.succ raise_id in
  let current_node_id = Node_id.succ enter_id in
  let current_var_id = 0 in
  let nodes = Node_id.Table.create () in
  let graph = G.create () in
  let temp_vars = Dvar.Table.create () in
  { current_node_id
  ; current_var_id
  ; nodes
  ; graph
  ; enter_id
  ; exit_id
  ; raise_id
  ; temp_vars
  }

