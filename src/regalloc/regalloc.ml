open! Core

open Z3i

include Regalloc_intf

module Make_constraint(Physical_register : Physical_register)
  : Register_constraint with module Physical_register = Physical_register =
struct
  module Physical_register = Physical_register

  module Argument = struct
    module Kind = struct
      module T = struct
        type t =
          | Input
          | Output
          | Temporary
        [@@deriving compare, sexp]
      end
      include T
      include Comparable.Make(T)
    end

    module T = struct
      type t =
        { kind : Kind.t
        ; index : int
        } [@@deriving compare, sexp]
    end
    include T
    include Comparable.Make(T)
  end

  type t =
    | Same of Argument.t * Argument.t
    | Distinct of Argument.Set.t
    | One_of of Argument.t * Physical_register.Set.t
    | Exactly of Argument.t * Physical_register.t

  [@@deriving sexp]

  module Soft = struct
    module Reward = struct
      type t =
        | Move
      [@@deriving sexp]
    end

    type nonrec t =
      { base : t
      ; reward : (int * Reward.t) list
      ; negate : bool
      } [@@deriving sexp]
  end
end

(* Register allocation using SAT solvers.

   Assign registers to variables in a graph of instructions, while obeying constraints
   that individual instructions have on registers, and spilling if necessary.

   An instruction has three sets of variables which must be assigned registers: inputs,
   outputs and temporaries.
   An output variable may be unused after the instruction, but must be assigned a register
   by the allocator (it is assumed that the instruction writes to all outputs).

   Inputs: Input variables must be produced by previous instructions (or be inputs into
   the graph). Multiple Inputs may refer to the same input variable.

   Outputs: All outputs must be distinct variables. Outputs can be assigned the same
   register as an input, but all outputs must be assigned a distinct register.
 *)

module Make_allocator
    (Variable_name : Variable_name)
    (Instruction : Instruction)
    (*
  : Allocator
    with module Variable_name = Variable_name
     and module Physical_register = Instruction_with_arguments.Instruction.Physical_register
     and module Instruction_with_arguments = Instruction_with_arguments
       *)
= struct

  module Physical_register = Instruction.Physical_register
  module Variable_name = Variable_name

  module Instruction_with_arguments = struct
    module Instruction = Instruction

    type 'v t =
      { instruction : Instruction.t
      ; inputs : 'v array
      ; outputs : 'v array
      } [@@deriving sexp_of]

    let map_vars
        { instruction
        ; inputs
        ; outputs
        }
        ~f
      =
      { instruction
      ; inputs = Array.map ~f inputs
      ; outputs = Array.map ~f outputs
      }

    let inputs_with_kind t =
      Array.fold2_exn
        ~init:Variable_name.Map.empty
        t.inputs
        (Instruction.Metadata.arguments_in (Instruction.metadata t.instruction))
        ~f:(fun acc vn kind ->
            Map.add acc ~key:vn ~data:kind
            |> function
            | `Duplicate ->
              assert (
                Physical_register.Kind.equal
                  (Map.find_exn acc vn)
                  kind
              );
              acc
            | `Ok map -> map
          )

    let outputs_with_kind t =
      Array.fold2_exn
        ~init:Variable_name.Map.empty
        t.outputs
        (Instruction.Metadata.arguments_out (Instruction.metadata t.instruction))
        ~f:(fun acc vn kind ->
            Map.add_exn acc ~key:vn ~data:kind
          )

    let create_move source target =
      { instruction = Instruction.create_move source target
      ; inputs = [| source |]
      ; outputs = [| target |]
      }

    let to_string arg_to_string t =
      let
        { instruction
        ; inputs
        ; outputs
        } = t
      in
      let inputs = Array.map inputs ~f:arg_to_string in
      let outputs = Array.map outputs ~f:arg_to_string in
      let left =
        match Array.length outputs with
        | 0 -> ""
        | 1 -> outputs.(0) ^ " = "
        | _ -> 
          "[" ^
          (String.concat_array ~sep:", " outputs)
          ^ "] = "
      in
      let instruction =
        Instruction.metadata instruction
        |> Instruction.Metadata.name
      in
      let right =
        match Array.length inputs with
        | 0 -> ""
        | _ ->
          " " ^ (String.concat_array ~sep:", " inputs)
      in
      left ^ instruction ^ right
           
  end

  module Node_id = Node_id

  module Instruction_node = struct
    module Edge = struct
      type 'n t =
        | Start
        | End
        | N of 'n
      [@@deriving sexp_of]

      let map ~f t =
        match t with
        | Start -> Start
        | End -> End
        | N n -> N (f n)
    end

    type 'v t =
      { i : 'v Instruction_with_arguments.t
      (* Mutable for creation *)
      (* CR smuenzel: make immutable *)
      ; mutable prev : 'v t Edge.t array
      ; mutable next : 'v t Edge.t array
      ; id : Node_id.t
      } [@@deriving fields]
    
    let sexp_of_t
        (type v)
        (sexp_of_v : v -> Sexp.t)
        { i
        ; prev
        ; next
        ; id = id'
        }
      =
      let prev = Array.map prev ~f:(Edge.map ~f:id) in
      let next = Array.map next ~f:(Edge.map ~f:id) in
      let id = id' in
      [%sexp
        { i : v Instruction_with_arguments.t
        ; prev : Node_id.t Edge.t array
        ; next : Node_id.t Edge.t array
        ; id : Node_id.t
        }
      ]
  end

  let number_of_physical_registers =
    Physical_register.all
    |> List.length

  module Register_mapping = struct
    type t =
      { set_sort : S.bv Sort.t
      ; set_of_kind : Bitvector.t Physical_register.Kind.Map.t
      ; preg_to_int : int Physical_register.Map.t
      ; int_to_preg : Physical_register.t Int.Map.t
      ; preg_to_set : Bitvector.t Physical_register.Map.t
      ; symbol_builder : Symbol_builder.t
      }

    let set_of_preg t preg =
      Map.find_exn t.preg_to_set preg

    let constrain_to_single_reg (_t : t) const =
      Bitvector.Set.has_single_member const

    let constrain_to_at_least_one_reg (_t : t) const =
      Boolean.not (Bitvector.Set.is_empty const)

    let distinct_registers (_t : t) constants =
      List.map constants
        ~f:(fun c ->
            List.init number_of_physical_registers
              ~f:(fun bit ->
                  Bitvector.extract_single c bit
                )
          )
      |> List.transpose_exn
      |> List.map ~f:(fun bitlist ->
          Bitvector.concat_list bitlist
          |> Bitvector.Set.has_max_one_member
        )

    let make_set_numeral_internal ~preg_to_int ~set_sort regs =
      (* CR smuenzel: little or big endian??? *)
      let s = Int.Set.map regs ~f:(Map.find_exn preg_to_int) in
      List.init number_of_physical_registers
        ~f:(fun i ->
            Set.mem s i
          )
      |> Bitvector.Numeral.bool (Sort.context set_sort)

    let make_set_numeral { preg_to_int; set_sort; _} regs =
      make_set_numeral_internal ~preg_to_int ~set_sort regs

    let make_set_constant t (opt : Optimize.t) kind =
      let constant =
        Expr.const_i
          (Symbol_builder.sym_int t.symbol_builder)
          t.set_sort
      in
      Optimize.add
        opt
        (Bitvector.Set.is_subset
           ~of_:(Map.find_exn t.set_of_kind kind) constant
        );
      constant

    let numeral_to_registers t num =
      Bitvector.Numeral.to_binary_array_exn num
      |> Array.filter_mapi ~f:(fun i bool ->
          if bool
          then Map.find t.int_to_preg i
          else None
        )

    let numeral_to_single_register_exn t num =
      numeral_to_registers t num
      |> function
      | [| single |] -> single
      | result -> raise_s [%message "not a single register"
                    (result : Physical_register.t array)
             ]

    let create (symbol_builder : Symbol_builder.t) : t =
      let context = Symbol_builder.context symbol_builder in
      let preg_to_int, int_to_preg =
        List.mapi Physical_register.all
          ~f:(Fn.flip Tuple2.create)
        |> Physical_register.Map.of_alist_exn
      , List.mapi Physical_register.all
          ~f:Tuple2.create
        |> Int.Map.of_alist_exn
      in
      let set_sort = Bitvector.create_sort context ~bits:number_of_physical_registers in
      let make_set_numeral = make_set_numeral_internal ~preg_to_int ~set_sort in
      let set_of_kind =
        Map.map
          Physical_register.all_by_kind
          ~f:make_set_numeral
      in
      let preg_to_set =
        List.map Physical_register.all
          ~f:(fun preg ->
              preg, make_set_numeral (Physical_register.Set.singleton preg)
            )
        |> Physical_register.Map.of_alist_exn
      in
      { set_sort
      ; set_of_kind
      ; preg_to_int
      ; int_to_preg
      ; preg_to_set
      ; symbol_builder
      }
  end


  module Constraint = struct
    include Instruction_with_arguments.Instruction.Metadata.Constraint

    let rec enforce (t : t) mapping ~argument_var =
      match t with 
      | Same (a,b) ->
        Boolean.eq (argument_var a) (argument_var b)
      | Distinct set ->
        Boolean.distinct
          (Set.to_list set |> List.map ~f:argument_var)
      | One_of (arg, rs) ->
        let arg = argument_var arg in
        Set.fold ~init:[] rs ~f:(fun acc r ->
            Boolean.eq
              arg (Register_mapping.set_of_preg mapping r)
            :: acc
          )
        |> Boolean.or_list
      | Exactly (arg, r) ->
        enforce (One_of (arg, Physical_register.Set.singleton r)) mapping ~argument_var
  end

  module Register_or_slot = struct
    type t =
      | Register of Physical_register.t
      | Reload_slot of Physical_register.Kind.t * int
    [@@deriving sexp]
  end

  module Register_or_reload = struct
    type t =
      | Register of Physical_register.t
      | Reload of
          { reload_slot : int
          ; temporary_register : Physical_register.t
          }
    [@@deriving sexp]
  end

  module Allocated_instruction = struct
    type t =
      | Original of
          { original_instruction_index : int
          ; inputs : Register_or_reload.t array
          ; outputs : Physical_register.t array
          ; temporaries : Physical_register.t array
          }
      | Spill of
          { register : Physical_register.t
          ; reload_slot : int
          }
      | Move of 
          { source : Physical_register.t
          ; destination : Physical_register.t
          }
    [@@deriving sexp]
  end

  module Allocation_result = struct
    type t =
      { instructions : Allocated_instruction.t array
      ; reload_slots_for_output : Physical_register.Kind.t array
      ; additional_reload_slots_in_block : Physical_register.Kind.t array
      ; inputs : Register_or_slot.t array
      ; outputs : Register_or_slot.t array
      } [@@deriving sexp]
  end

  module Variable_allocation_constraint = struct
    type t =
      | This of Register_or_slot.t
      | Choose of Physical_register.Kind.t
    [@@deriving sexp]
  end

  module Liveness = struct

    let array_rev_foldi array ~f ~init =
      let acc = ref init in
      let length = Array.length array in
      for i = length - 1 downto 0 do
        acc := f i !acc array.(i);
      done;
      !acc

    type 'v t =
      { mutable at_input : 'v
      ; reads : 'v
      ; defines : 'v
      ; mutable at_output : 'v
      ; node : Variable_name.t Instruction_node.t
      ; is_enter : bool
      ; is_exit : bool
      }

    module Immutable = struct
      type 'v t =
        { at_input : 'v
        ; reads : 'v
        ; defines : 'v
        ; at_output : 'v
        ; node : Variable_name.t Instruction_node.t
        ; is_enter : bool
        ; is_exit : bool
        } [@@deriving sexp_of]

      let map t ~f =
        { t
            with
              at_input = f t.at_input
            ; reads = f t.reads
            ; defines = f t.defines
            ; at_output = f t.at_output
          }
    end

    let to_immutable
        { at_input
        ; reads
        ; defines
        ; at_output
        ; node
        ; is_enter : bool
        ; is_exit : bool
        } =
      { Immutable.
        at_input
      ; reads
      ; defines
      ; at_output
      ; node
      ; is_enter : bool
      ; is_exit : bool
      }

    let create_from_graph
        ~(input : Physical_register.Kind.t Variable_name.Map.t)
        ~(output : Physical_register.Kind.t Variable_name.Map.t)
        (instructions : Variable_name.t Instruction_node.t array)
      =
      let liveness_by_node_id = Node_id.Table.create () in
      let visited = Node_id.Table.create () in
      let variable_kinds = Variable_name.Table.create () in
      let add_variable_map, add_variable_array =
        let if_not_found key data _ =
          Hashtbl.add_exn variable_kinds ~key ~data
        in
        let maybe_add key data =
          Hashtbl.find_and_call2
            variable_kinds
            key
            ~a:data
            ~b:key
            ~if_found:(fun current_kind other_kind variable_name ->
                if not (Physical_register.Kind.equal current_kind other_kind)
                then raise_s [%message "register kind mismatch"
                      (variable_name : Variable_name.t)
                      (current_kind : Physical_register.Kind.t)
                      (other_kind : Physical_register.Kind.t)
                  ]
              )
            ~if_not_found
        in
        let add_variable_map m =
          Map.iteri m
            ~f:(fun ~key ~data -> maybe_add key data)
        in
        let add_variable_array names kinds =
          Array.iter2_exn names kinds
            ~f:maybe_add
        in
        add_variable_map, add_variable_array
      in
      add_variable_map input;
      add_variable_map output;
      let end_nodes =
        Array.fold instructions
          ~init:[]
          ~f:(fun acc
               ({ Instruction_node.
                  i; id; prev; next
                } as node) ->
               Hashtbl.add_exn visited ~key:id ~data:false;
               let m = Instruction.metadata i.instruction in
               add_variable_array i.inputs (Instruction.Metadata.arguments_in m);
               add_variable_array i.outputs (Instruction.Metadata.arguments_out m);
               let at_input = Variable_name.Set.of_array i.inputs in
               let at_output = Variable_name.Set.of_array i.outputs in
               let is_enter = Array.mem prev Start ~equal:Poly.equal in
               let reads = at_input in
               let defines = at_output in
               let at_input =
                 if is_enter
                 then Set.union at_input (Map.key_set input)
                 else at_input
               in
               let is_exit = Array.mem next End ~equal:Poly.equal in
               let at_output, is_end_node =
                 if is_exit
                 then Set.union at_output (Map.key_set output)
                    , true
                 else at_output
                    , false
               in
               let data =
                 { at_input
                 ; reads
                 ; defines
                 ; at_output
                 ; node
                 ; is_enter
                 ; is_exit
                 }
               in
               Hashtbl.add_exn liveness_by_node_id ~key:id ~data;
               if is_end_node
               then node :: acc
               else acc
             )
      in
      assert Poly.(end_nodes <> []);
      let changed = ref true in
      let rec backpropagate_node (node : _ Instruction_node.t) =
        if Hashtbl.find_exn visited node.id
        then ()
        else begin
          Hashtbl.set visited ~key:node.id ~data:true;
          let liveness =
            Hashtbl.find_exn liveness_by_node_id node.id
          in
          let output_without_defines =
            Set.diff
              liveness.at_output
              liveness.defines
          in
          let new_input =
            Set.union
              output_without_defines
              liveness.at_input
          in
          if not (Set.equal new_input liveness.at_input)
          then begin
            changed := true;
            liveness.at_input <- new_input;
          end;
          Array.iter node.prev
            ~f:(function
                | Start -> ()
                | End -> assert false
                | N prev_node ->
                  let prev_liveness =
                    Hashtbl.find_exn liveness_by_node_id prev_node.id
                  in
                  let new_prev_output =
                    Set.union
                      prev_liveness.at_output
                      new_input
                  in
                  if not
                      (Set.equal new_prev_output prev_liveness.at_output)
                  then begin
                    changed := true;
                    prev_liveness.at_output <- new_prev_output;
                  end;
                  backpropagate_node prev_node
              )
        end
      in
      while !changed do
        changed := false;
        Hashtbl.map_inplace visited ~f:(fun _ -> false);
        List.iter end_nodes ~f:backpropagate_node
      done;
      (* CR smuenzel: need some asserts, matching start and end *)
      Hashtbl.map liveness_by_node_id ~f:to_immutable
    , variable_kinds

    let create
        ~(input : Physical_register.Kind.t Variable_name.Map.t)
        ~(output : Physical_register.Kind.t Variable_name.Map.t)
        (instructions : Variable_name.t Instruction_with_arguments.t array)
      =
      let current_live, live_list =
        array_rev_foldi
          ~init:(output, [ output ])
          instructions
          ~f:(fun i (next_live, live_list) instruction ->
              let without_outputs =
                Map.merge
                  next_live
                  (Instruction_with_arguments.outputs_with_kind instruction)
                  ~f:(fun ~key:variable me ->
                      match me with
                      | `Right _ -> 
                        (* CR smuenzel: Do something in this case?*)
                        None
                      | `Left x -> Some x
                      | `Both (next_kind, output_kind) ->
                        if Physical_register.Kind.equal next_kind output_kind
                        then None
                        else
                          raise_s [%message "physical register kind mismatch"
                              ~instruction_index:(i : int)
                              (next_kind : Physical_register.Kind.t)
                              (output_kind : Physical_register.Kind.t)
                              (variable : Variable_name.t)
                          ]
                    )
              in
              let with_inputs =
                Map.merge
                  without_outputs
                  (Instruction_with_arguments.inputs_with_kind instruction)
                  ~f:(fun ~key:variable me ->
                      match me with
                      | `Right x | `Left x -> Some x
                      | `Both (next_kind, input_kind) ->
                        if Physical_register.Kind.equal next_kind input_kind
                        then Some next_kind
                        else
                          raise_s [%message "physical register kind mismatch"
                              ~instruction_index:(i : int)
                              (next_kind : Physical_register.Kind.t)
                              (input_kind : Physical_register.Kind.t)
                              (variable : Variable_name.t)
                          ]
                    )

              in
              let prev_live = with_inputs in
              prev_live, prev_live :: live_list
            )
      in
      if not (Map.equal Physical_register.Kind.equal current_live input)
      then begin
        raise_s [%message "non-input variable live at beginning of block"
          ~extra_live_variables:(Set.diff (Map.key_set current_live) (Map.key_set input) : Variable_name.Set.t)
        ]
      end;
      Array.of_list live_list

    let all_variables a =
      Array.fold a ~init:Variable_name.Set.empty
        ~f:Set.union
  end

  module Parameters = struct
    type t =
      { move_penalty : int
      ; reload_cost : int
      } [@@deriving sexp]

    let default =
      { move_penalty = 1
      ; reload_cost = 10
      }

    let compute_reward t (r : (int * Constraint.Soft.Reward.t) list) =
      let { move_penalty
          ; reload_cost = _
          } = t
      in
      List.fold r ~init:0
        ~f:(fun acc (mul, reward) ->
            assert (mul > 0);
            let base =
              match reward with
              | Move -> move_penalty
            in
            (mul * base) + acc
          )
  end

  module Z3_assist = struct
    let add_move_count_penalty
        (opt : Optimize.t)
        symbol_builder
        (p : Parameters.t)
        ~prev
        ~next
      =
      let size = Bitvector.size_e prev in
      List.init size
        ~f:(fun bit ->
            let has_move =
              Bitvector.and_
                (Bitvector.not (Bitvector.extract_single prev bit))
                (Bitvector.extract_single next bit)
            in
            Optimize.add_soft
              opt
              ~weight:p.move_penalty
              (Bitvector.is_zero has_move)
              (Symbol_builder.sym symbol_builder)
          )

    let add_reload_penalty
        (opt : Optimize.t)
        symbol_builder
        (p : Parameters.t)
        ~prev
        ~prev_spill
        ~next
        ~next_spill
        =
      let has_reload =
        Boolean.and_list
          [ Bitvector.is_zero prev
          ; Bitvector.is_not_zero prev_spill
          ; Bitvector.is_not_zero next
          ]
      in
      let no_spill =
        Bitvector.is_zero
          (Bitvector.and_
             (Bitvector.not prev_spill)
             next_spill)
      in
      [ Optimize.add_soft opt
          ~weight:p.move_penalty
          no_spill
          (Symbol_builder.sym symbol_builder)
      ; Optimize.add_soft opt
          ~weight:p.reload_cost
          (Boolean.not has_reload)
          (Symbol_builder.sym symbol_builder)
      ]
  end

  let array_iter_pairs a ~f =
    for i = 0 to Array.length a - 2 do
      f a.(i) a.(i+1)
    done

  let array_map_pairs a ~f =
    let len = Array.length a - 1 in
    if len = 0 
    then [||]
    else begin
      let first = f a.(0) a.(1) in 
      let result = Array.create ~len first in
      for i = 1 to Array.length a - 2 do
        result.(i) <- f a.(i) a.(i+1)
      done;
      result
    end

  let array_map3_exn a0 a1 a2 ~f =
    let l0 = Array.length a0 in
    assert (l0 = Array.length a1);
    assert (l0 = Array.length a2);
    Array.init l0 ~f:(fun i -> f Array.(unsafe_get a0 i) Array.(unsafe_get a1 i) Array.(unsafe_get a2 i))

  let array_iter3_exn a0 a1 a2 ~f =
    let l0 = Array.length a0 in
    assert (l0 = Array.length a1);
    assert (l0 = Array.length a2);
    for i = 0 to pred l0 do
      f Array.(unsafe_get a0 i) Array.(unsafe_get a1 i) Array.(unsafe_get a2 i)
    done

  let debug = false

  module Register_state = struct
    type 'a t =
      { before : 'a
      ; after : 'a
      } [@@deriving sexp]

    let iter { before; after } ~f =
      f before;
      f after

    let map { before; after } ~f =
      { before = f before
      ; after = f after
      }
  end

  module Allocation_variable = struct
    type t =
      { reg_set : Bitvector.t
      ; spill : Bitvector.t
      } [@@deriving fields]

    let constrain_to_single_reg mapping t =
      Register_mapping.constrain_to_single_reg
        mapping
        t.reg_set

    let constrain_to_single_reg_no_spill mapping t =
      Boolean.and_
        (Register_mapping.constrain_to_single_reg
            mapping
            t.reg_set)
        (Bitvector.is_zero t.spill)

    let constrain_to_at_least_one_reg mapping t =
      Register_mapping.constrain_to_at_least_one_reg 
        mapping
        t.reg_set

    let constrain_to_at_least_one_location mapping t =
      Boolean.or_
        (Register_mapping.constrain_to_at_least_one_reg 
            mapping
            t.reg_set)
        (Bitvector.is_not_zero t.spill)

    let constrain_to_single_location mapping t =
      Boolean.xor
        (Register_mapping.constrain_to_single_reg
            mapping
            t.reg_set
        )
        (Bitvector.is_not_zero t.spill)

    let distinct_registers mapping ts =
      Register_mapping.distinct_registers
        mapping
        (List.map ts ~f:reg_set)

    let is_subset t ~of_ =
      Boolean.and_
        (Bitvector.Set.is_subset t.reg_set ~of_:of_.reg_set)
        (Bitvector.Set.is_subset t.spill ~of_:of_.spill)

    let const_e_exn model t =
      { reg_set = Model.const_interp_e_exn model t.reg_set
      ; spill = Model.const_interp_e_exn model t.spill
      }

    let numeral_to_single_register_exn register_mapping t =
      Register_mapping.numeral_to_single_register_exn register_mapping t.reg_set

    let numeral_spill t =
      (Bitvector.Numeral.to_binary_array_exn t.spill).(0)

    let numeral_to_registers register_mapping t =
      Register_mapping.numeral_to_registers register_mapping t.reg_set
    , numeral_spill t

    module Model = struct
      type t' = t
      type t =
        { reg_set : Physical_register.Set.t
        ; spill : bool
        } [@@deriving sexp_of]

      let const_e_exn model register_mapping (t' : t') =
        let t' = const_e_exn model t' in
        let reg_set, spill =
          numeral_to_registers register_mapping t'
        in
        let reg_set = Physical_register.Set.of_array reg_set in
        { reg_set
        ; spill
        }
    end

    module Move = struct
      type t =
        | Reg : { from : Physical_register.t
                ; to_ : Physical_register.t
                } -> t
        | Spill of Physical_register.t
        | Reload of Physical_register.t
      [@@deriving sexp_of]

      let infer
          ~input:{ Model. reg_set = reg_set_in; spill = spill_in}
          ~output:{ Model. reg_set = reg_set_out; spill = spill_out}
        =
        let spill =
          if spill_out && not spill_in
          then begin
            [ Spill (Set.choose_exn reg_set_in)
            ]
          end
          else []
        in
        let reload =
          if spill_in && Set.is_empty reg_set_in && not (Set.is_empty reg_set_out)
          then
            Set.to_list reg_set_out
            |> List.map ~f:(fun r -> Reload r)
          else []
        in
        let regular =
          if not (Set.is_empty reg_set_in)
          then begin
            let from = Set.choose_exn reg_set_in in
            Set.diff reg_set_out reg_set_in
            |> Set.to_list
            |> List.map ~f:(fun to_ ->
                Reg { from; to_ }
              )
          end
          else []
        in
        List.concat
          [ spill
          ; reload
          ; regular
          ]

    end
  end

  let allocate_basic_block_internal 
      ?(parameters = Parameters.default)
      ~(input)
      ~(output)
      (instructions : Variable_name.t Instruction_with_arguments.t array)
      symbol_builder
    =
    ignore parameters;
    let opt = Optimize.create (Symbol_builder.context symbol_builder) in
    let register_mapping = Register_mapping.create symbol_builder in
    let create_allocation_variable kind =
      { Allocation_variable.reg_set =
          Register_mapping.make_set_constant
            register_mapping
            opt
            kind
      ; spill = Bitvector.const ~bits:1 (Symbol_builder.sym symbol_builder)
      }
    in
    let liveness = Liveness.create ~input ~output instructions in
    if debug
    then print_s [%message "liveness" ~_:(liveness : Physical_register.Kind.t Variable_name.Map.t array)]
    ;
    let liveness_vars_per_instruction =
      let make vars =
        Map.map vars
          ~f:create_allocation_variable
      in
      let liveness =
        array_map_pairs liveness
          ~f:(fun before after ->
              { Register_state.
                before = make before
              ; after = make after
              })
      in
      Array.map2_exn liveness instructions
        ~f:(fun liveness inst ->
            (* After must include outputs, even if not live! *)
            let arguments_out =
              Instruction_with_arguments.outputs_with_kind inst
            in
            let missing_outputs =
              Map.filter_mapi arguments_out
                ~f:(fun ~key:output ~data:kind ->
                    match Map.find liveness.after output with
                    | Some _ -> None
                    | None ->
                      Some (create_allocation_variable kind)
                  )
            in
            let after =
              Map.merge_skewed
                liveness.after
                missing_outputs
                ~combine:(fun ~key:_ _ _ -> assert false)
            in
            { liveness with after }
          )
    in
    (* Penalize moves *)
    array_iter_pairs liveness_vars_per_instruction 
      ~f:(fun { after; _} { before; _} ->
          Map.iter2 after before
            ~f:(fun ~key:_ ~data ->
                match data with
                | `Left _ | `Right _ -> ()
                | `Both 
                    ({ Allocation_variable.
                       reg_set = prev
                     ; spill = prev_spill
                     }
                    ,{ Allocation_variable.
                       reg_set = next
                     ; spill = next_spill
                     }) ->
                  Z3_assist.add_move_count_penalty opt symbol_builder parameters
                    ~prev ~next
                  |> (ignore : S.bool Optimize.Goal.t list -> unit)
                  ;
                  Z3_assist.add_reload_penalty opt symbol_builder parameters
                    ~prev
                    ~prev_spill
                    ~next
                    ~next_spill
                  |> (ignore : S.bool Optimize.Goal.t list -> unit)
                  ;
              )
         )
    ;
    (* Make sure reg sets are valid and distinct *)
    Array.iter liveness_vars_per_instruction
      ~f:(Register_state.iter
            ~f:(fun vars ->
                Map.map vars
                  ~f:(Allocation_variable.constrain_to_at_least_one_location
                        register_mapping
                     )
                |> Map.data
                |> Optimize.add_list opt
                ;
                Allocation_variable.distinct_registers
                  register_mapping
                  (Map.data vars)
                |> Optimize.add_list opt
              )
         )
    ;
    let constrain_to_single_reg vars =
      Map.map vars
        ~f:(Allocation_variable.constrain_to_single_reg_no_spill
              register_mapping
           )
      |> Map.data
      |> Optimize.add_list opt
    in
    let instruction_inputs =
      (* Explicit inputs, since we may need to select from multiple registers *)
      Array.map2_exn instructions liveness_vars_per_instruction
        ~f:(fun { inputs; instruction; _ } { Register_state. before; _ } ->
            let input_vars = 
              Instruction.Metadata.arguments_in
                (Instruction.metadata instruction)
              |> Array.map
                (* CR smuenzel: maybe just registers not spilled vars? *)
                ~f:create_allocation_variable
            in
            Array.iter2_exn inputs input_vars
              ~f:(fun vname vvar ->
                  [ Allocation_variable.is_subset
                      vvar
                      ~of_:(Map.find_exn before vname)
                  ; Allocation_variable.constrain_to_single_reg register_mapping vvar
                  ] |> Optimize.add_list opt
                );
            input_vars
          )
    in
    (* CR smuenzel: use move penalty instead for first instruction? or insert nop?  *)
    constrain_to_single_reg liveness_vars_per_instruction.(0).before;
    constrain_to_single_reg liveness_vars_per_instruction.(Array.length liveness_vars_per_instruction - 1).after;
    Array.iter liveness_vars_per_instruction
      ~f:(fun { Register_state.before; after } ->
          Map.iter2 before after
            ~f:(fun ~key:_ ~data ->
                match data with
                | `Left _ -> ()
                | `Right output ->
                  (* Outputs should be single reg *)
                  Allocation_variable.constrain_to_single_reg_no_spill register_mapping output
                  |> Optimize.add opt
                | `Both (before, after) ->
                  (* No implicit moves through instructions, only destruction of
                     variables allowed *)
                  Allocation_variable.is_subset after ~of_:before
                  |> Optimize.add opt
               )
        );
    array_iter3_exn
      instructions
      instruction_inputs
      liveness_vars_per_instruction
      ~f:(fun inst inst_inputs register_state ->
          let argument_var (a : Constraint.Argument.t) =
            match a with
            | { kind = Input ; index } ->
              inst_inputs.(index).reg_set
            | { kind = Output; index } ->
              (Map.find_exn register_state.after inst.outputs.(index)).reg_set
            | { kind = Temporary; _ } ->
              assert false
          in
          let metadata =
            Instruction.metadata inst.instruction
          in
          Instruction.Metadata.constraints
            metadata
          |> Array.iter
            ~f:(fun constr ->
                Constraint.enforce
                  constr
                  register_mapping
                  ~argument_var
                |> Optimize.add opt
              );
          let destroyed =
            Instruction.Metadata.destroys
              metadata
          in
          if not (Set.is_empty destroyed)
          then begin
            let destroyed =
              Register_mapping.make_set_numeral
                register_mapping
                destroyed
            in
            Map.iter
              register_state.after
              ~f:(fun allocation_variable ->
                  Bitvector.and_
                    allocation_variable.reg_set
                    destroyed
                  |> Bitvector.is_zero
                  |> Optimize.add opt
                )
          end;
          Instruction.Metadata.soft_constraints
            metadata
          |> Array.iter
            ~f:(fun constr ->
                let reward = Parameters.compute_reward parameters constr.reward in
                let negate =
                  if constr.negate
                  then Boolean.not
                  else Fn.id
                in
                let c =
                  Constraint.enforce
                    constr.base
                    register_mapping
                    ~argument_var
                  |> negate
                in
                Optimize.add_soft opt ~weight:reward c (Symbol_builder.sym symbol_builder)
                |> (ignore : S.bool Optimize.Goal.t -> unit)
              );
        )
    ;
    if debug
    then print_endline (Optimize.to_string opt);
    Optimize.check_current_and_get_model opt
    |> Solver_result.map
      ~f:(fun model ->
          let before_and_after =
            Array.map liveness_vars_per_instruction
              ~f:(Register_state.map
                    ~f:(fun vars ->
                        Map.map vars ~f:(Allocation_variable.const_e_exn model)
                      )
                 )
          in
          let instruction_inputs =
            Array.map instruction_inputs
              ~f:(Array.map ~f:(Allocation_variable.const_e_exn model))
          in
          array_map3_exn
            instructions instruction_inputs before_and_after
            ~f:(fun { Instruction_with_arguments.
                      instruction
                    ; inputs
                    ; outputs
                    }
                 input_vars
                 before_and_after
                 ->
                   let inputs = 
                     assert (Array.length inputs = Array.length input_vars);
                     input_vars
                     |> Array.map
                          ~f:(Allocation_variable.numeral_to_single_register_exn register_mapping)
                   in
                   let outputs =
                     Array.map outputs ~f:(Map.find_exn before_and_after.after)
                     |> Array.map
                          ~f:(Allocation_variable.numeral_to_single_register_exn register_mapping)
                   in
                   let before_and_after =
                     Register_state.map before_and_after
                       ~f:(Map.map ~f:(Allocation_variable.numeral_to_registers register_mapping))
                   in
                   { Instruction_with_arguments.
                     inputs
                   ; outputs
                   ; instruction
                   }, before_and_after
              )
        )

  let allocate_basic_block _ = assert false

  module Move_edge = struct
    type t =
      { node_in : Node_id.t Instruction_node.Edge.t 
      ; node_out : Node_id.t Instruction_node.Edge.t 
      ; moves : Allocation_variable.Move.t list Variable_name.Map.t
      } [@@deriving sexp_of]

    let create
        ~node_in
        ~node_out
        ~(input : Allocation_variable.Model.t Variable_name.Map.t)
        ~(output : Allocation_variable.Model.t Variable_name.Map.t)
      =
      let moves =
        Map.merge input output
          ~f:(fun ~key m ->
              match m with
              | `Left _ -> None
              | `Right _ ->
                if false
                then
                  raise_s [%message "only output" (key: Variable_name.t)]
                ;
                None
              | `Both (input, output) ->
                Allocation_variable.Move.infer
                  ~input
                  ~output
                |> function
                | [] -> None
                | list -> Some list
            )
      in
      if Map.is_empty moves
      then None
      else Some {node_in; node_out; moves}

    let create_all
        ~(variable_states : Allocation_variable.Model.t Variable_name.Map.t Liveness.Immutable.t Node_id.Table.t)
        ~(input_states : Allocation_variable.Model.t Variable_name.Map.t)
        ~(output_states : Allocation_variable.Model.t Variable_name.Map.t)
      =
      if Hashtbl.is_empty variable_states
      then begin
        [ create
          ~node_in:Start
          ~node_out:End
          ~input:input_states
          ~output:output_states
        ]
        |> List.filter_opt
      end else begin
        Hashtbl.fold variable_states
          ~init:[]
          ~f:(fun ~key ~data acc ->
              let l =
                (if data.is_enter
                 then
                   create
                     ~node_in:Start
                     ~node_out:(N key)
                     ~input:input_states
                     ~output:data.at_input
                 else None
                )
                :: (if data.is_exit
                    then
                      create
                        ~node_in:(N key)
                        ~node_out:End
                        ~input:data.at_output
                        ~output:output_states
                    else None
                   )
                :: (
                  Array.fold data.node.next
                    ~init:[]
                    ~f:(fun acc next ->
                        match next with
                        | Start | End -> acc
                        | N next ->
                          let next_id = next.id in
                          let next = Hashtbl.find_exn variable_states next_id in
                          create
                            ~node_in:(N key)
                            ~node_out:(N next_id)
                            ~input:data.at_output
                            ~output:next.at_input
                          :: acc
                      )
                )
                |> List.filter_opt
              in
              List.concat [ l; acc ]
            )
      end

  end

  type t =
    { variable_states : Allocation_variable.Model.t Variable_name.Map.t Liveness.Immutable.t Node_id.Table.t
    ; input_states : Allocation_variable.Model.t Variable_name.Map.t
    ; output_states : Allocation_variable.Model.t Variable_name.Map.t
    ; moves : Move_edge.t list
    }

  let allocate_graph_internal
      ?(parameters = Parameters.default)
      ~(input)
      ~(output)
      (instructions : Variable_name.t Instruction_node.t array)
      symbol_builder
    =
    ignore parameters;
    let opt = Optimize.create (Symbol_builder.context symbol_builder) in
    let register_mapping = Register_mapping.create symbol_builder in
    let liveness, register_kinds =
      Liveness.create_from_graph
        ~input
        ~output
        instructions
    in
    let create_allocation_variable_k kind =
      { Allocation_variable.reg_set =
          Register_mapping.make_set_constant
            register_mapping
            opt
            kind
      ; spill = Bitvector.const (Symbol_builder.sym symbol_builder) ~bits:1
      }
    in
    let create_allocation_variable name =
      create_allocation_variable_k
        (Hashtbl.find_exn register_kinds name)
    in
    let make vars =
      Map.of_key_set vars
        ~f:create_allocation_variable
    in
    let variable_states =
      Hashtbl.map liveness
        ~f:(fun 
             { at_input
             ; at_output
             ; reads
             ; defines
             ; node
             ; is_enter
             ; is_exit
             } ->
             let at_input = make at_input in
             let reads = make reads in
             let at_output = make at_output in
             let defines =
               Variable_name.Map.of_key_set defines ~f:(Map.find_exn at_output)
             in
             { Liveness.Immutable.
               at_input
             ; at_output
             ; reads
             ; defines
             ; node
             ; is_enter
             ; is_exit
             }
          )
    in
    let input_states =
      Map.map input ~f:create_allocation_variable_k
    in
    let output_states =
      Map.map output ~f:create_allocation_variable_k
    in
    let alloc_constraint map apply =
      Map.data map
      |> List.map
        ~f:(apply
              register_mapping
           )
    in
    (* Distinct registers *)
    let distinct_registers_map map =
      Allocation_variable.distinct_registers
        register_mapping
        (Map.data map)
      |> Optimize.add_list opt
    in
    distinct_registers_map input_states;
    distinct_registers_map output_states;
    Hashtbl.iter variable_states
      ~f:(fun { at_input; at_output; _ } ->
          distinct_registers_map at_input;
          distinct_registers_map at_output;
        );
    (* Each variable has a location *)
    Hashtbl.iter variable_states
      ~f:(fun { at_output; at_input; _ } ->
          alloc_constraint
            at_output
            Allocation_variable.constrain_to_at_least_one_location
          |> Optimize.add_list opt;
          alloc_constraint
            at_input
            Allocation_variable.constrain_to_at_least_one_location
          |> Optimize.add_list opt;
        );
    (* Outputs are single registers, inputs are registers *)
    Hashtbl.iter variable_states
      ~f:(fun { reads; defines; at_input; _ } ->
          alloc_constraint
            defines
            Allocation_variable.constrain_to_single_reg_no_spill
          |> Optimize.add_list opt;
          alloc_constraint
            reads
            Allocation_variable.constrain_to_single_reg
          |> Optimize.add_list opt;
          (* Our chosen input register to read needs to be one of the
             locations of the input *)
          Map.iter2 at_input reads
              ~f:(fun ~key:_ ~data ->
                match data with
                | `Right _ | `Left _ -> ()
                | `Both (at_input, read) ->
                  Allocation_variable.is_subset read ~of_:at_input
                  |> Optimize.add opt
              )
        );
    (* Global inputs are single registers *)
    alloc_constraint
      input_states
      Allocation_variable.constrain_to_single_reg_no_spill
    |> Optimize.add_list opt;
    (* Global outputs have a single location *)
    alloc_constraint
      output_states
      Allocation_variable.constrain_to_single_location
    |> Optimize.add_list opt;
    (* Variables don't move during instructions *)
    Hashtbl.iter variable_states
      ~f:(fun { at_input; at_output; _ } ->
          Map.iter2 at_input at_output
              ~f:(fun ~key:_ ~data ->
                match data with
                | `Right _ | `Left _ -> ()
                | `Both (input, output) ->
                  Allocation_variable.is_subset output ~of_:input
                  |> Optimize.add opt
              )
        )
    ;
    (* Move penalty *)
    let add_move_and_reload_penalty ~from ~to_ ~var ~prev ~next =
      if debug
      then begin
        Printf.printf
          !"%{sexp:Node_id.t Instruction_node.Edge.t} -> %{sexp:Node_id.t Instruction_node.Edge.t} : %{Variable_name}\n"
          from to_ var
      end;
      let { Allocation_variable.
            reg_set = prev
          ; spill = prev_spill
          } = prev 
      in
      let { Allocation_variable.
            reg_set = next
          ; spill = next_spill
          } = next
      in
      Z3_assist.add_move_count_penalty opt symbol_builder parameters
        ~prev ~next
      |> (ignore : S.bool Optimize.Goal.t list -> unit)
      ;
      Z3_assist.add_reload_penalty opt symbol_builder parameters
        ~prev
        ~prev_spill
        ~next
        ~next_spill
      |> (ignore : S.bool Optimize.Goal.t list -> unit)
      ;
    in
    let add_move_and_reload_penalty ~from ~to_ ~prev ~next =
      Map.iter2
        prev
        next
        ~f:(fun ~key:var ~data ->
            match data with
            | `Right _ | `Left _ -> ()
            | `Both (prev, next) ->
              add_move_and_reload_penalty ~from ~to_ ~var ~prev ~next
          )
    in
    Hashtbl.iter variable_states
      ~f:(fun { at_input; at_output; node; is_exit; _ } ->
          if is_exit
          then add_move_and_reload_penalty ~from:(N node.id) ~to_:End ~prev:at_output ~next:output_states;
          Array.iter node.prev
            ~f:(function
                | Start ->
                  add_move_and_reload_penalty
                    ~from:Start
                    ~to_:(N node.id)
                    ~prev:input_states
                    ~next:at_input
                | End -> assert false
                | N { id = prev_id; _ } ->
                  let prev_outputs = (Hashtbl.find_exn variable_states prev_id).at_output in
                  add_move_and_reload_penalty
                    ~from:(N prev_id)
                    ~to_:(N node.id)
                    ~prev:prev_outputs
                    ~next:at_input
              );
          ()
        );
    (* Instruction constraints *)
    Hashtbl.iter variable_states
      ~f:(fun { node; reads; defines; _ } ->
          let metadata = Instruction.metadata node.i.instruction in
          let constraints = Instruction.Metadata.constraints metadata in
          let soft_constraints = Instruction.Metadata.soft_constraints metadata in
          match constraints, soft_constraints with
          | [||], [||] -> ()
          | constraints, soft_constraints ->
            let inputs = Array.map node.i.inputs ~f:(Map.find_exn reads) in
            let outputs = Array.map node.i.outputs ~f:(Map.find_exn defines) in
            let argument_var : Constraint.Argument.t -> _ = function
              | { kind = Constraint.Argument.Kind.Input; index } -> inputs.(index).reg_set
              | { kind = Constraint.Argument.Kind.Output; index } -> outputs.(index).reg_set
              | { kind = Constraint.Argument.Kind.Temporary; index = _ } -> assert false
            in
            Array.iter constraints
              ~f:(fun c ->
                  Constraint.enforce
                    c
                    register_mapping
                    ~argument_var
                  |> Optimize.add opt
                );
            Array.iter soft_constraints
              ~f:(fun c ->
                  let reward = Parameters.compute_reward parameters c.reward in
                  let negate =
                    if c.negate
                    then Boolean.not
                    else Fn.id
                  in
                  let c =
                  Constraint.enforce
                    c.base
                    register_mapping
                    ~argument_var
                  |> negate
                  in
                  Optimize.add_soft opt ~weight:reward c (Symbol_builder.sym symbol_builder)
                  |> (ignore : S.bool Optimize.Goal.t -> unit)
                );
        );
    (* Instruction destroys *)
    Hashtbl.iter variable_states
      ~f:(fun { node; at_output; _ } ->
          let metadata = Instruction.metadata node.i.instruction in
          let destroyed =
            Instruction.Metadata.destroys
              metadata
          in
          if not (Set.is_empty destroyed)
          then begin
            let destroyed =
              Register_mapping.make_set_numeral
                register_mapping
                destroyed
            in
            Map.iter
              at_output
              ~f:(fun allocation_variable ->
                  Bitvector.and_
                    allocation_variable.reg_set
                    destroyed
                  |> Bitvector.is_zero
                  |> Optimize.add opt
                )
          end;
        );
    (* Non-SSA support: when an instruction modifies a variable, it can only be in
       one spot in the input *)
    Hashtbl.iter variable_states
      ~f:(fun { reads; defines; at_input; _} ->
          Map.iter2
            reads
            defines
            ~f:(fun ~key:var ~data ->
                match data with
                | `Right _ | `Left _ -> ()
                | `Both (_,_) ->
                  Map.find_exn at_input var
                  |> Allocation_variable.constrain_to_single_location
                       register_mapping
                  |> Optimize.add opt
              )
        );
    (* CR smuenzel: do we need this? *)
    (* When there are multiple paths to a node, force sources of inputs to only have a
       single location *)
    if false
    then begin
      Hashtbl.iter variable_states
        ~f:(fun { node; _ } -> 
            if Array.length node.prev > 1
            then begin
              Array.iter node.prev
                ~f:(function
                    | Start | End -> ()
                    | N node ->
                      Map.iter
                        (Hashtbl.find_exn variable_states node.id).at_output
                        ~f:(fun v ->
                            Allocation_variable.constrain_to_single_location
                              register_mapping
                              v
                            |> Optimize.add opt
                          )
                  )
            end
          )
    end
    ;
    (* Find solution *)
    if debug
    then print_endline (Optimize.to_string opt);
    Optimize.check_current_and_get_model opt
    |> Solver_result.map
      ~f:(fun model ->
          let get_model a =
            Allocation_variable.Model.const_e_exn model register_mapping a
          in
          let variable_states =
            Hashtbl.map
              variable_states
              ~f:(Liveness.Immutable.map
                    ~f:(Map.map ~f:get_model))
          in
          let input_states = Map.map ~f:get_model input_states in
          let output_states = Map.map ~f:get_model output_states in
          let moves =
            Move_edge.create_all
              ~variable_states
              ~input_states
              ~output_states
          in
          { variable_states
          ; input_states
          ; output_states
          ; moves
          }
        )
end
