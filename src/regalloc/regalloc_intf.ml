open! Core

module type Physical_register_kind = sig
  type t [@@deriving equal, compare, sexp]

  include Comparable.S with type t := t
end

module type Physical_register = sig
  module Kind : Physical_register_kind

  type t [@@deriving equal, compare, enumerate, sexp]

  include Comparable.S with type t := t

  val kind : t -> Kind.t

  val all_by_kind : Set.t Kind.Map.t

end

module type Register_constraint = sig
  module Physical_register : Physical_register

  module Argument : sig
    module Kind : sig
      type t =
        | Input
        | Output
        | Temporary
      [@@deriving sexp]

      include Comparable.S with type t := t
    end

    type t =
      { kind : Kind.t
      ; index : int
      } [@@deriving sexp]

    include Comparable.S with type t := t
  end

  type t =
    | Same of Argument.t * Argument.t
    | Distinct of Argument.Set.t
    | One_of of Argument.t * Physical_register.Set.t
    | Exactly of Argument.t * Physical_register.t
  [@@deriving sexp]

  module Soft : sig
    module Reward : sig
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

module type Instruction_metadata = sig
  module Physical_register : Physical_register
  module Constraint : Register_constraint
    with module Physical_register := Physical_register

  type t
  val name : t -> string

  val arguments_in : t -> Physical_register.Kind.t array
  val arguments_out : t -> Physical_register.Kind.t array
  val temporaries : t -> Physical_register.Kind.t array

  val constraints : t -> Constraint.t array
  val soft_constraints : t -> Constraint.Soft.t array
  val destroys : t -> Physical_register.Set.t
end

module type Instruction = sig
  module Physical_register : Physical_register
  module Metadata : Instruction_metadata
    with module Physical_register := Physical_register

  type t [@@deriving sexp_of]

  val metadata : t -> Metadata.t

  val create_move : Physical_register.t -> Physical_register.t -> t

end

module type Variable_name = sig
  type t [@@deriving equal, compare, sexp_of]

  val to_string : t -> string

  include Comparable.S_plain with type t := t
  include Hashable.S_plain with type t := t
end

module type Instruction_with_arguments = sig
  module Instruction : Instruction

  type 'v t =
    { instruction : Instruction.t
    ; inputs : 'v array
    ; outputs : 'v array
    }
end

module Node_id = Unique_id.Int()
  
module type Instruction_node = sig
  module Instruction_with_arguments : Instruction_with_arguments

  module Edge : sig
    type 'n t =
      | Start
      | End
      | N of 'n
  end

  type 'v t =
    { i : 'v Instruction_with_arguments.t
    ; prev : 'v t Edge.t array
    ; next : 'v t Edge.t array
    ; id : Node_id.t
    }
end

module type Allocator = sig
  module Physical_register : Physical_register
  module Variable_name : Variable_name
  module Instruction_with_arguments : Instruction_with_arguments
    with module Instruction.Physical_register = Physical_register
  module Instruction_node : Instruction_node
    with module Instruction_with_arguments := Instruction_with_arguments

  module Register_or_slot : sig
    type t =
      | Register of Physical_register.t
      | Reload_slot of Physical_register.Kind.t * int
    [@@deriving sexp]
  end

  module Register_or_reload : sig
    type t =
      | Register of Physical_register.t
      | Reload of
          { reload_slot : int
          (* CR smuenzel: allow instructions to use reload slots directly *)
          ; temporary_register : Physical_register.t
          }
  end

  module Allocated_instruction : sig
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
  end

  module Allocation_result : sig
    type t =
      { instructions : Allocated_instruction.t array
      ; reload_slots_for_output : Physical_register.Kind.t array
      ; additional_reload_slots_in_block : Physical_register.Kind.t array
      ; inputs : Register_or_slot.t array
      ; outputs : Register_or_slot.t array
      }
  end

  module Variable_allocation_constraint : sig
    type t =
      | This of Register_or_slot.t
      | Choose of Physical_register.Kind.t
  end

  val allocate_basic_block
    :  Variable_name.t Instruction_with_arguments.t array
    -> inputs:Variable_allocation_constraint.t Variable_name.Map.t
    -> outputs:Variable_allocation_constraint.t Variable_name.Map.t
    -> Allocation_result.t Or_error.t
end

