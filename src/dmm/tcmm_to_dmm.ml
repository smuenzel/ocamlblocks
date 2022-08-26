open Core

module Cmm = Ocamlc_kit.Cmm

module Dmm = Dmm_intf

module Node_id = Dmm.Node_id

module Dvar = Dmm.Dvar
module Dinst = Dmm.Dinst
module Trap_stack = Dmm.Trap_stack

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

(*
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
   l*)

let rec transl
    (b : Dmm.Inst_args.t Igraph_builder.t)
    (cmm : Tcmm.Texpr.t)
    ~(this_id:Node_id.t)
    ~(fallthrough_id:Node_id.t)
    (exits : (Node_id.t * (Dvar.t * Cmm.machtype) list) Int.Map.t)
    ~trap_stack
    ~(result:Dvar.t option)
  =
  match cmm with
  | T (Cconst_int (int, _dbg), _output_type) ->
    let int = Nativeint.of_int_exn int in
    Igraph_builder.insert b ~next:[| fallthrough_id |]
      this_id
      { inst = Pure (I (Const int))
      ; inputs = [||]
      ; output = result
      ; trap_stack
      }
  | T (Cconst_natint (int, _dbg), _output_type) ->
    Igraph_builder.insert b ~next:[| fallthrough_id |]
      this_id
      { inst = Pure (I (Const int))
      ; inputs = [||]
      ; output = result
      ; trap_stack
      }
  | T (Cconst_float (f,_), _output_type) ->
    Igraph_builder.insert b ~next:[| fallthrough_id |]
      this_id
      { inst = Pure (F (Const f))
      ; inputs = [||]
      ; output = result
      ; trap_stack
      }
  | T (Cconst_symbol (s, _), _output_type) ->
    Igraph_builder.insert b ~next:[| fallthrough_id |]
      this_id
      { inst = Pure (Symbol s)
      ; inputs = [||]
      ; output = result
      ; trap_stack
      }
  | T (Cvar v, _output_type) ->
    Igraph_builder.insert b ~next:[| fallthrough_id |]
      this_id
      { inst = Move
      ; inputs = [| v |]
      ; output = result
      ; trap_stack
      }
  | T (Clet (var, (T (_, bexpr_t) as bexpr), expr), _output_type)
  | T (Clet_mut (var, bexpr_t, bexpr, expr), _output_type) ->
    let expr_id = Igraph_builder.next_id b in
    let destination = [ var, bexpr_t ] in
    transl_var_exprs b
      ~source:[ bexpr ]
      ~destination
      ~this_id
      ~fallthrough_id:expr_id
      exits
      ~trap_stack
    ;
    transl b expr
      ~this_id:expr_id
      ~fallthrough_id
      exits
      ~result
      ~trap_stack
  | T (Cassign (v, expr), _output_type) ->
    transl b expr
      ~this_id
      ~fallthrough_id
      exits
      ~result:(Some v)
      ~trap_stack
  | T (Ctuple [], _) ->
    Igraph_builder.insert b
      this_id
      ~next:[| fallthrough_id |]
      { inst = Nop
      ; inputs = [||]
      ; output = None
      ; trap_stack
      }
  | T (Ctuple exprs, _output_type) ->
    let destination =
      List.map exprs
        ~f:(fun (T (_,typ)) ->
            Igraph_builder.temp b typ, typ
          )
    in
    let combine_id = Igraph_builder.next_id b in
    transl_var_exprs b
      ~source:exprs
      ~destination
      ~this_id
      ~fallthrough_id:combine_id
      exits
      ~trap_stack
    ;
    Igraph_builder.insert b ~next:[| fallthrough_id |]
      combine_id
      { inst = Pure Assemble_tuple
      ; inputs = List.map ~f:fst destination |> Array.of_list
      ; output = result
      ; trap_stack
      }
  | T (Csequence (expr_a, expr_b), _typ) ->
    let first_id = Igraph_builder.next_id b in
    let second_id = Igraph_builder.next_id b in
    transl
      b expr_a ~this_id:first_id ~fallthrough_id:second_id exits ~result:None ~trap_stack;
    transl b expr_b ~this_id:second_id ~fallthrough_id exits ~result ~trap_stack;
    ()
  | T (Cifthenelse (discriminator, _ , ifso, _, ifnot, _), _) ->
    let cond_id = Igraph_builder.next_id b in
    let test, args =
      transl_test
        b
        discriminator
        ~this_id
        ~cond_id
        exits
        ~trap_stack
    in
    let ifso_id = Igraph_builder.next_id b in
    let ifnot_id = Igraph_builder.next_id b in
    transl b ifso ~this_id:ifso_id ~fallthrough_id exits ~result ~trap_stack;
    transl b ifnot ~this_id:ifnot_id ~fallthrough_id exits ~result ~trap_stack;
    Igraph_builder.insert b
      cond_id
      { inst = Flow (Test_and_branch test)
      ; inputs = args
      ; output = None
      ; trap_stack
      }
      ~next:[| ifso_id; ifnot_id |]
  | T (Cswitch (discriminator, indices, targets, _dbg), _typ) ->
    let target_ids =
      Array.map targets
        ~f:(fun (cmm, _dbg) ->
            let id = Igraph_builder.next_id b in
            transl b cmm ~this_id:id ~fallthrough_id exits ~result ~trap_stack;
            id
          )
    in
    let T (_,switcher_typ) = discriminator in
    let switcher = Igraph_builder.temp b switcher_typ in
    let switcher_id = Igraph_builder.next_id b in
    transl
      b discriminator ~this_id ~fallthrough_id:switcher_id 
      exits ~result:(Some switcher) ~trap_stack
    ;
    Igraph_builder.insert b
      this_id
      { inst = Flow (Switch indices)
      ; inputs = [| switcher |]
      ; output = None
      ; trap_stack
      }
      ~next:target_ids
  | T (Ccatch (rec_flag, catches, expr), _) ->
    let catches_map =
      List.fold catches
        ~init:Int.Map.empty
        ~f:(fun acc (exit_id, args, _expr, _dbg) ->
            Map.add_exn acc ~key:exit_id ~data:(Igraph_builder.next_id b, args)
          )
    in
    let all_exits =
      Map.merge_skewed exits catches_map
        ~combine:(fun ~key:_ _ _ -> assert false)
    in
    transl b expr ~this_id ~fallthrough_id all_exits ~result ~trap_stack;
    let exit_rec =
      match rec_flag with
      | Recursive -> all_exits
      | Nonrecursive -> exits
    in
    List.iter catches
      ~f:(fun (exit_id, _args, expr, _dbg) ->
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
            ~trap_stack
        )
    ;
    ()
  | T (Cexit (exit_number, args), _) ->
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
          ~trap_stack
    end
  | T (Ctrywith (body, _exn, handler, _dbg) , _) ->
    let new_trap_stack = Trap_stack.add_fresh_trap trap_stack in
    let trap_adjust_id = Igraph_builder.next_id b in
    Igraph_builder.insert b ~next:[| fallthrough_id |]
      trap_adjust_id
      { inst = Nop
      ; inputs = [||]
      ; output = None
      ; trap_stack
      }
    ;
    transl
      b
      body
      ~this_id
      ~fallthrough_id:trap_adjust_id
      exits
      ~trap_stack:new_trap_stack
      ~result
    ;
    let pre_handler_id = Igraph_builder.next_id b in
    let handler_id = Igraph_builder.next_id b in
    (* Insert Nop so that the Poptrap happens in the handler *)
    Igraph_builder.insert b ~next:[| handler_id |]
      pre_handler_id
      { inst = Nop
      ; inputs = [||]
      ; output = None
      ; trap_stack = new_trap_stack
      }
    ;
    transl b handler ~this_id:handler_id ~fallthrough_id exits ~trap_stack ~result;
    ()
  | T (Cop (_op, T (Cconst_symbol (func, _dbg), _) :: expr ,_),_) ->
    (* CR smuenzel: a little hacky to match on arguments, should be done in an earlier
       translation *)
    let op_start_id = Igraph_builder.next_id b in
    let destination =
      List.map expr
        ~f:(fun (T (_, dtyp)) -> Igraph_builder.temp b dtyp, dtyp)
    in
    transl_var_exprs
      b
      ~source:expr
      ~destination
      ~this_id
      ~fallthrough_id:op_start_id
      exits
      ~trap_stack
    ;
    let inputs = Array.of_list_map ~f:fst destination in
    let tail =
      (* CR smuenzel: this means we can't insert no-ops after *)
      Node_id.equal fallthrough_id (Igraph_builder.exit_id b)
    in
    Igraph_builder.insert b ~next:[| fallthrough_id |]
      op_start_id
      { inst = Call (Call_immediate { func; tail })
      ; inputs
      ; output = result
      ; trap_stack
      }
    ;
    ()
  | T (Cop (op, expr, _dbg), _) ->
    let op_start_id = Igraph_builder.next_id b in
    let destination =
      List.map expr
        ~f:(fun (T (_, dtyp)) -> Igraph_builder.temp b dtyp, dtyp)
    in
    transl_var_exprs
      b
      ~source:expr
      ~destination
      ~this_id
      ~fallthrough_id:op_start_id
      exits
      ~trap_stack
    ;
    let inputs = Array.of_list_map ~f:fst destination in
    transl_op
      b
      op
      ~inputs
      ~this_id:op_start_id
      ~fallthrough_id
      ~trap_stack
      ~result
    ;
    ()

and transl_op
    (b : _ Igraph_builder.t)
    (cmm : Cmm.operation)
    ~inputs
    ~(this_id:Node_id.t)
    ~(fallthrough_id:Node_id.t)
    ~trap_stack
    ~result
  =
  let dmm_op, next =
    match cmm with
    | Craise kind ->
      Dmm.Dinst.Flow (Raise kind), Some (Igraph_builder.raise_id b)
    | Capply _ ->
      let tail =
        (* CR smuenzel: this means we can't insert no-ops after *)
        Node_id.equal fallthrough_id (Igraph_builder.exit_id b)
      in
      Call (Call_indirect { tail }), None
    | Cextcall (func, ty_res, ty_args, alloc) ->
      let ty_args = Array.of_list ty_args in
      Call (Call_ext { func; ty_res; ty_args; alloc }), None
    | Cload { memory_chunk; mutability; is_atomic } ->
      Mem (Load { memory_chunk; mutability; is_atomic }), None
    | Calloc ->
      Mem Alloc, None
    | Cstore (memory_chunk, init) ->
      Mem (Store { memory_chunk; init }), None
    | Caddi | Caddv | Cadda ->
      Pure (I Add), None
    | Csubi ->
      Pure (I Sub), None
    | Cmuli ->
      Pure (I Mul), None
    | Cmulhi ->
      Pure (I Mulh), None
    | Cdivi ->
      Pure (I Div), None
    | Cmodi ->
      Pure (I Mod), None
    | Cand ->
      Pure (I And), None
    | Cor ->
      Pure (I Or), None
    | Cxor ->
      Pure (I Xor), None
    | Clsl ->
      Pure (I Lsl), None
    | Clsr ->
      Pure (I Lsr), None
    | Casr ->
      Pure (I Asr), None
    | Ccmpi comparison
    | Ccmpa comparison ->
      Pure (I (Cmp { signed = true; comparison})), None
    | Cnegf ->
      Pure (F Neg), None
    | Cabsf ->
      Pure (F Abs), None
    | Caddf ->
      Pure (F Add), None
    | Csubf ->
      Pure (F Sub), None
    | Cmulf ->
      Pure (F Mul), None
    | Cdivf ->
      Pure (F Div), None
    | Cfloatofint ->
      Pure (F Of_int), None
    | Cintoffloat ->
      Pure (F To_int), None
    | Ccmpf comparison ->
      Pure (F (Cmp comparison)), None
    | Ccheckbound ->
      Flow Checkbound, None
    | Copaque ->
      Opaque, None
    | Cdls_get ->
      Mem Dls_get, None
  in
  let next = Option.value ~default:fallthrough_id next in
  Igraph_builder.insert b
    this_id
    ~next:[| next |]
    { inst = dmm_op
    ; inputs
    ; output = result
    ; trap_stack
    }
  ;
  ()

and transl_test
    (b : _ Igraph_builder.t)
    (cmm : Tcmm.Texpr.t)
    ~(this_id:Node_id.t)
    ~(cond_id:Node_id.t)
    exits
    ~trap_stack
  =
  (* CR smuenzel: This should expand complex tests in a target-specific way *)
  let test_result = Igraph_builder.temp b Cmm.typ_int in
  transl b cmm ~this_id ~fallthrough_id:cond_id exits ~trap_stack
    ~result:(Some test_result)
  ;
  Dmm_intf.Test.Bool { then_value = true }, [| test_result |]

and transl_var_exprs
    (b : _ Igraph_builder.t)
    ~(source:Tcmm.Texpr.t list)
    ~(destination:(Dvar.t * Cmm.machtype) list)
    ~(this_id:Node_id.t)
    ~(fallthrough_id:Node_id.t)
    exits
    ~trap_stack
  =
  match source, destination with
  | [], [] ->
    Igraph_builder.insert b
      this_id
      ~next:[| fallthrough_id |]
      { inst = Nop
      ; inputs = [||]
      ; output = None
      ; trap_stack
      }
    ;
  | [], _ :: _ -> assert false
  | _ :: _, [] -> assert false
  | s :: ss, (d, _dtyp) :: ds ->
    let next_id = Igraph_builder.next_id b in
    transl b
      ~this_id
      s
      ~fallthrough_id:next_id
      ~result:(Some d)
      exits
      ~trap_stack
    ;
    transl_var_exprs
      b
      ~source:ss
      ~destination:ds
      ~this_id:next_id
      ~fallthrough_id
      exits
      ~trap_stack



