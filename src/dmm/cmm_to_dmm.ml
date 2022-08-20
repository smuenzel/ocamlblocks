open Core

module Cmm = Ocamlc_kit.Cmm

module Dmm = Dmm_intf

module Node_id = Dmm.Node_id

module Dvar = Dmm.Dvar

module Igraph_builder = Dmm.Igraph_builder

module Id_maker : sig
  type t
  val create : unit -> t
  val next : t -> Node_id.t
end = struct
  type t = Node_id.t ref

  let create () = ref Node_id.zero
  let next t =
    let v = !t in
    t := Node_id.succ v;
    v
end

module Insert_result : sig 
  type t [@@immediate]

  val join : t -> t -> t
  val ignore : t -> unit
end = struct
  type t = unit
  let join () () = ()
  let ignore = Fn.id
end

let rec create_moves
    (b : Igraph_builder.t)
    ~(source:Dvar.t list)
    ~(destination:Dvar.t list)
    ~(this_id:Node_id.t)
    ~(fallthrough_id:Node_id.t)
  =
  match source, destination with
  | [], [] ->
    Igraph_builder.insert b
      this_id
      ~next:[| fallthrough_id |]
      { inst = Nop
      ; inputs = [||]
      ; output = None
      }
    ;
  | [], _ :: _ -> assert false
  | _ :: _, [] -> assert false
  | s :: ss, d :: ds ->
    let next_id = 
      if Dvar.equal s d
      then this_id
      else begin
        let next_id = Igraph_builder.next_id b in
        Igraph_builder.insert b
          this_id
          { inst = Move
          ; inputs = [| s |]
          ; output = Some d
          }
          ~next:[| next_id |]
        ;
        next_id
      end
    in
    create_moves
      b
      ~source:ss
      ~destination:ds
      ~this_id:next_id
      ~fallthrough_id

let rec transl
    (b : Igraph_builder.t)
    (cmm : Cmm.expression)
    ~(this_id:Node_id.t)
    ~(fallthrough_id:Node_id.t)
    (exits : (Node_id.t * Dvar.t list) Int.Map.t)
    ~(result:Dvar.t option)
  =
  match cmm with
  | Cconst_int (int, _dbg) ->
    Igraph_builder.insert b
      this_id
      { inst = Pure (I (Const int))
      ; inputs = [||]
      ; output = result
      }
      ~next:[| fallthrough_id |]
  | Cexit (exit_number, args) ->
    begin match Map.find exits exit_number with
      | None -> assert false
      | Some (exit_destination, vars) ->
        transl_var_exprs
          b
          ~source:args
          ~destination:vars
          ~this_id
          ~fallthrough_id:exit_destination
          exits
    end
  | Csequence (expr_a, expr_b) ->
    let first_id = Igraph_builder.next_id b in
    let second_id = Igraph_builder.next_id b in
    transl b expr_a ~this_id:first_id ~fallthrough_id:second_id exits ~result:None;
    transl b expr_b ~this_id:second_id ~fallthrough_id exits ~result;
    ()
  | Cifthenelse (discriminator, _ , ifso, _, ifnot, _) ->
    let cond_id = Igraph_builder.next_id b in
    let test, args =
      transl_test
        b
        discriminator
        ~this_id
        ~cond_id
        exits
    in
    let ifso_id = Igraph_builder.next_id b in
    let ifnot_id = Igraph_builder.next_id b in
    transl b ifso ~this_id:ifso_id ~fallthrough_id exits ~result;
    transl b ifnot ~this_id:ifnot_id ~fallthrough_id exits ~result;
    Igraph_builder.insert b
      cond_id
      { inst = Flow (Test_and_branch test)
      ; inputs = args
      ; output = None
      }
      ~next:[| ifso_id; ifnot_id |]
  | Ccatch 
      ( rec_flag
      , catches
      , expr
      ) ->
    let catches_map =
      List.fold catches
        ~init:Int.Map.empty
        ~f:(fun acc (exit_id, args, _expr, _dbg) ->
            let args =
              List.map args
                ~f:(fun (v, _) ->
                    Dvar.Var (Backend_var.With_provenance.var v)
                  )
            in
            Map.add_exn acc ~key:exit_id ~data:(Igraph_builder.next_id b, args)
          )
    in
    let all_exits =
      Map.merge_skewed exits catches_map
        ~combine:(fun ~key:_ _ _ -> assert false)
    in
    transl b expr ~this_id ~fallthrough_id all_exits ~result;
    let exit_rec =
      match rec_flag with
      | Recursive -> all_exits
      | Nonrecursive -> exits
    in
    List.iter catches
      ~f:(fun (exit_id, args, expr, _dbg) ->
          let this_id =
            fst (Map.find_exn catches_map exit_id)
          in
          transl
            b
            expr
            ~this_id
            ~fallthrough_id
            exit_rec
            ~result
        )
    ;
    ()
  | _ -> ()
and transl_test
    (b : Igraph_builder.t)
    (cmm : Cmm.expression)
    ~(this_id:Node_id.t)
    ~(cond_id:Node_id.t)
    exits
  =
  assert false
and transl_var_exprs
    (b : Igraph_builder.t)
    ~(source:Cmm.expression list)
    ~(destination:Dvar.t list)
    ~(this_id:Node_id.t)
    ~(fallthrough_id:Node_id.t)
    exits
  =
  match source, destination with
  | [], [] ->
    Igraph_builder.insert b
      this_id
      ~next:[| fallthrough_id |]
      { inst = Nop
      ; inputs = [||]
      ; output = None
      }
    ;
  | [], _ :: _ -> assert false
  | _ :: _, [] -> assert false
  | s :: ss, d :: ds ->
    let next_id = Igraph_builder.next_id b in
    transl b
      ~this_id
      s
      ~fallthrough_id:next_id
      ~result:(Some d)
      exits
    ;
    transl_var_exprs
      b
      ~source:ss
      ~destination:ds
      ~this_id:next_id
      ~fallthrough_id
      exits



