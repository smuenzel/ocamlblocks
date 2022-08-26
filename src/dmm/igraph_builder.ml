open! Core

module Cmm = Ocamlc_kit.Cmm

module Dmm = Dmm_intf

module Dvar = Dmm.Dvar

module Node_id = Dmm.Node_id

module G = Graph.Imperative.Digraph.ConcreteBidirectional(Node_id)

module Node = struct
  type 'a t =
    { contents : 'a
    ; next : Node_id.t array
    }
end

type 'a t =
  { mutable current_node_id : Node_id.t 
  ; mutable current_var_id : int
  ; nodes : 'a Node.t Node_id.Table.t
  ; graph : (G.t [@sexp.opaque])
  ; enter_id : Node_id.t
  ; exit_id : Node_id.t
  ; raise_id : Node_id.t
  ; temp_vars : Cmm.machtype Dvar.Table.t
  } [@@deriving fields]

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
           let { Node. contents = c ; next } = Hashtbl.find_exn nodes node_id in
           [%sexp
             { node_id : Node_id.t
             ; next : Node_id.t array
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

let to_dot { nodes; exit_id; raise_id; _ } ~f =
  let b = Buffer.create 1000 in
  Buffer.add_string b "digraph igraph {\n";
  Hashtbl.iteri nodes
    ~f:(fun ~key ~data:{ Node. contents; next } ->
        Printf.sprintf "%i [ label = \"%s\"];\n" (Node_id.to_int key) (f contents)
        |> Buffer.add_string b;
        Array.iter next
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
  let node =
    { Node.
      contents = value
    ; next
    }
  in
  Hashtbl.add_exn t.nodes ~key:node_id ~data:node;
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

