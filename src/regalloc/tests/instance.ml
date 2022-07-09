open! Core
open! Blocks_regalloc

module Instruction = struct
  module Physical_register = struct
    module Kind = struct
      module T = struct
        type t =
          | General
        [@@deriving compare, sexp, equal, enumerate]
      end
      include T
      include Comparable.Make(T)
    end

    module T = struct
      type t =
        | R0
        | R1
        | R2
        | R3
      [@@deriving compare, sexp, equal, enumerate]
    end
    include T

    include Comparable.Make(T)

    let all_by_kind = Kind.Map.of_alist_exn [ General, Set.of_list all ]

    let kind (_ : t) = Kind.General

    let to_string t = Sexp.to_string ([%sexp_of: t] t)
  end

  module Opcode = struct
    type t =
      | Nop
      | Load
      | Store
      | Move
      | Add
      | Addo
      | Loop
    [@@deriving sexp]
  end

  module Metadata = struct
    module Constraint = Regalloc.Make_constraint(Physical_register)

    include Opcode

    let name t = Sexp.to_string ([%sexp_of: t] t)

    let constraints = function
      | Addo | Loop ->
        [| Constraint.Same ({ kind = Input; index = 0}, { kind = Output; index = 0}) |]
      | _ -> [||]

    let soft_constraints = function
      | Move ->
        [| { Constraint.Soft.
             base = Same ({ kind = Input; index = 0}, { kind = Output; index = 0})
           ; reward = [ 1,Move ]
           ; negate = false
           }
        |]
      | _ -> [||]

    let temporaries _ = [||]

    let arguments_out : t -> Physical_register.Kind.t array = function
      | Load | Store | Add | Move | Addo ->
        [| General |]
      | Nop -> [||]
      | Loop -> [| General |]

    let arguments_in : t -> Physical_register.Kind.t array = function
      | Load | Store | Move | Loop ->
        [| General |]
      | Add | Addo ->
        [| General; General |]
      | Nop -> [||]

    let destroys _ = Physical_register.Set.empty
  end

  type t = Opcode.t [@@deriving sexp_of]

  let metadata t = t

  let create_move _ _ = Opcode.Move
end

module Physical_register = Instruction.Physical_register

module Regalloc = Regalloc.Make_allocator(String)(Instruction)

module Register_state = Regalloc.Register_state
module Instruction_with_arguments = Regalloc.Instruction_with_arguments
