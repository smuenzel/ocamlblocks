open Core

module Cmm = Ocamlc_kit.Cmm
module Asttypes = Ocamlc_kit.Asttypes

module Call = struct
  type t =
    | Extcall
    | Call_immediate of { func : string; tail : bool }
    | Call_indirect of { tail : bool }
    | Call_ext of 
        { func : string
        ; ty_res : Cmm.machtype
        ; ty_args : Cmm.exttype array
        ; alloc : bool
        }
  [@@deriving sexp_of]
end

module Test = struct
  type t =
    | Bool of { then_value : bool }
    | Integer of { signed : bool; comparison : Cmm.integer_comparison }
    | Float of Cmm.float_comparison
    | Parity of { even : bool }
  [@@deriving sexp_of]
end

module Control_flow = struct
  type t =
    | End
    | Return
    | Test_and_branch of Test.t
    | Switch of int array
    | Raise of Lambda.raise_kind
    | Checkbound
  [@@deriving sexp_of]
end

module Pure_op = struct
  module Integer = struct
    type t =
      | Add
      | Sub
      | Mul
      | Mulh
      | Div
      | Mod
      | And
      | Or
      | Xor
      | Lsl
      | Lsr
      | Asr
      | Cmp of { signed : bool; comparison : Cmm.integer_comparison }
      | Const of Nativeint.t
    [@@deriving sexp_of]
  end

  module Float = struct
    type t =
      | Neg
      | Abs
      | Add
      | Sub
      | Mul
      | Div
      | Of_int
      | To_int
      | Cmp of Cmm.float_comparison
      | Const of float
    [@@deriving sexp_of]
  end

  type t =
    | I of Integer.t
    | F of Float.t
    | Symbol of string
    | Assemble_tuple
  [@@deriving sexp_of]
end

module Mem_op = struct
  type t =
    | Load of
        { memory_chunk: Cmm.memory_chunk
        ; mutability: Asttypes.mutable_flag
        ; is_atomic: bool
        }
    | Store of
        { memory_chunk : Cmm.memory_chunk
        ; init : Lambda.initialization_or_assignment
        }
    | Alloc
    | Dls_get
  [@@deriving sexp_of]
end

module Dinst = struct
  type t =
    | Flow of Control_flow.t
    | Call of Call.t
    | Pure of Pure_op.t
    | Mem of Mem_op.t
    | Move
    | Opaque
    | Trap of { direction : [ `Enter | `Leave ] }
    | Nop
  [@@deriving sexp_of]
end

module Node_id : sig
  type t [@@immediate]

  val zero : t
  val succ : t -> t
  val of_int : int -> t
  val to_int : t -> int

  val equal : t -> t -> bool

  include Hashable.S_plain with type t := t

end = struct
  include Int
end

module Trap_id = Unique_id.Int()

module Trap_stack = struct
  type t = Trap_id.t list [@@deriving sexp_of]

  let add_fresh_trap t =
    Trap_id.create () :: t
end

type t =
  { id : Node_id.t
  ; inst : Dinst.t
  ; args : unit array
  ; next : Node_id.t array
  }

module Backend_var = struct
  include Backend_var
  let hash_fold_t s t =
    Hash.fold_int s (hash t)

  let sexp_of_t t =
    Sexp.Atom (Backend_var.unique_name t)
end

module Dvar = struct
  module T = struct
    type t =
      | Temp of int
      | Var of Backend_var.t
    [@@deriving hash, compare, sexp_of]
  end
  include T
  include Hashable.Make_plain(T)

  let equal a b =
    match a, b with
    | Temp _, Var _ -> false
    | Var _, Temp _ -> false
    | Temp a, Temp b -> Int.equal a b
    | Var a, Var b -> Backend_var.equal a b
end

module Inst_args = struct
  type t =
    { inst : Dinst.t
    ; inputs : Dvar.t array
    ; output : Dvar.t option
    ; trap_stack : Trap_stack.t
    } [@@deriving sexp_of]
end

module Inst_notrap = struct
  (* CR smuenzel: maybe [Inst.With_trap], [Inst] *)

  type t =
    { inst : Dinst.t
    ; inputs : Dvar.t array
    ; output : Dvar.t option
    }

end

