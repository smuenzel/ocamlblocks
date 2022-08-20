open Core

module Cmm = Ocamlc_kit.Cmm

module Call = struct
  type t =
    | Extcall
    | Call_immediate of { func : string; tail : bool }
    | Call_indirect of { tail : bool }
    | Call_ext of 
        { func : string
        ; res : Cmm.machtype
        ; args : Cmm.exttype array
        ; alloc : bool
        ; stack_ofs : int
        }

end

module Test = struct
  type t =
    | Bool of { then_value : bool }
    | Integer of { signed : bool; comparison : Cmm.integer_comparison }
    | Float of Cmm.float_comparison
    | Parity of { even : bool }
end

module Control_flow = struct
  type t =
    | End
    | Return
    | Test_and_branch of Test.t
    | Switch
    | Raise
    | Checkbound
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
      | Const of int
  end

  module Float = struct
    type t

  end

  type t =
    | I of Integer.t
    | F of Float.t

end

module Mem_op = struct
  type t =
    | Load
    | Store
    | Alloc
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
end

module Node_id : sig
  type t [@@immediate]

  val zero : t
  val succ : t -> t
  val of_int : int -> t
  val to_int : t -> int

end = struct
  type t = int
  let succ = succ
  let zero = 0
  let of_int = Fn.id
  let to_int = Fn.id
end

type t =
  { id : Node_id.t
  ; inst : Dinst.t
  ; args : unit array
  ; next : Node_id.t array
  }

module Dvar = struct
  type t =
    | Temp of int
    | Var of Backend_var.t

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
    }
end

module Igraph_builder : sig
  type t

  val next_id : t -> Node_id.t
  val temp : t -> Dvar.t

  val insert : t -> Node_id.t -> Inst_args.t -> next:Node_id.t array -> unit

end = struct
  type t

  let next_id _ = assert false
  let temp _ = assert false
  let insert _ _ _ ~next:_ = assert false

end
