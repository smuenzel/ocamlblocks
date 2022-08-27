open! Core

module Dmm = Dmm_intf 

let remove_trap (b : Dmm.Inst_args.t Igraph_builder.t) =
  (* CR smuenzel: we modify b, maybe we should restore it? copy first? *)
  let b = Igraph_builder.map ~f:Fn.id b in
  Igraph_builder.update_edge_targets b
    ~f:(fun ~from:_ ~from_node ~edge_index:_ ~to_ ~to_node ->
        let to_trap_stack =
          match to_node with
          | None -> Dmm.Trap_stack.empty
          | Some to_node -> to_node.trap_stack
        in
        if Dmm.Trap_stack.equal from_node.trap_stack to_trap_stack
        then None
        else begin
          match
            Dmm.Trap_stack.trap_delta
              ~source:from_node.trap_stack ~destination:to_trap_stack
          with
          | `Nothing -> assert false
          | `Push _ -> assert false
          | `Pop pop_count ->
            let next_ids =
              to_
              :: List.init pop_count ~f:(fun _ -> Igraph_builder.next_id b)
              |> List.rev
            in
            let rec iter = function
              | id :: (id_next :: _ as rest) ->
                Igraph_builder.insert b
                  id 
                  ~next:[| id_next |]
                  { inst = Trap { direction = `Leave }
                  ; inputs = [||]
                  ; output = None
                  ; trap_stack = to_trap_stack
                  }
                ;
                iter rest
              | _ :: [] | [] -> ()
            in
            iter next_ids;
            Some (List.hd_exn next_ids)
        end
      );
  Igraph_builder.map b
    ~f:(fun { inst; inputs; output; trap_stack = _ } ->
        { Dmm.Inst_notrap.
          inst
        ; inputs
        ; output
        }
      )


