open! Core
open! Blocks_regalloc
open! Ocamlc_kit
open! Asmcomp_platform_shared

module Make(Platform : Platform_intf.S) = struct
  open Platform

  module Physical_register_kind = struct
    module T = struct
      type t = int [@@deriving compare]

      let num_register_classes = Proc.num_register_classes

      module Machtype_component = struct
        type t = Cmm.machtype_component =
          | Val
          | Addr 
          | Int
          | Float
        [@@deriving sexp, enumerate]
      end

      let class_names =
        List.map Machtype_component.all
          ~f:(fun typ ->
              Proc.register_class
                { Reg.dummy with typ
                }
            , typ
            )
        |> Int.Map.of_alist_multi
        |> Map.map ~f:(fun list ->
            List.map list ~f:(fun c -> Sexp.to_string ([%sexp_of:Machtype_component.t] c))
            |> String.concat
          )

      let t_of_class_name =
        Map.to_alist class_names |> List.map ~f:Tuple2.swap |> String.Map.of_alist_exn

      let all = Map.keys class_names

      let sexp_of_t t = Sexp.Atom (Map.find_exn class_names t)
      let t_of_sexp s = Core.Map.find_exn t_of_class_name ([%of_sexp: string] s)

      let () = assert (num_register_classes = Map.length class_names)
    end
    include T

    include Comparable.Make(T)
  end

  module _ : Regalloc_intf.Physical_register_kind = Physical_register_kind

  module Physical_register = struct
    module Kind = Physical_register_kind

    module T = struct
      type t = int [@@deriving compare]

      let by_kind =
        Array.map2_exn
          Proc.first_available_register
          Proc.num_available_registers
          ~f:(fun first count ->
              List.init count ~f:(fun i -> first + i)
            )

      let sexp_of_t t = Sexp.Atom (Proc.register_name t)

      let all =
        Array.to_list by_kind
        |> List.concat_no_order

      let by_name =
        all
        |> List.map ~f:(fun r -> Proc.register_name r, r)
        |> String.Map.of_alist_exn

      let t_of_sexp t =
        Map.find_exn by_name ([%of_sexp: string] t)
    end
    include T
    include Comparable.Make(T)

    let all_by_kind =
      Array.map by_kind ~f:Set.of_list
      |> Array.to_list
      |> List.mapi ~f:Tuple2.create
      |> Kind.Map.of_alist_exn


    let kind_by_t =
      all_by_kind
      |> Core.Map.fold ~init:Map.empty
        ~f:(fun ~key:kind ~data acc ->
            Set.fold ~init:acc data
              ~f:(fun acc reg ->
                  Map.add_exn acc ~key:reg ~data:kind
                )
          )

    let kind t = Map.find_exn kind_by_t t
  end

  module _ : Regalloc_intf.Physical_register = Physical_register

  module Variable_name = struct
    module T = struct
      type t = Reg.t

      let compare a b = Int.compare a.Reg.stamp b.Reg.stamp

      let to_string t =
        Printf.sprintf "%s/%i" (Reg.name t) t.stamp

      let sexp_of_t t =
        Sexp.Atom (to_string t)

      let hash_fold_t s t = Int.hash_fold_t s t.Reg.stamp

      let hash t = Int.hash t.Reg.stamp

    end
    include T
    include Comparable.Make_plain(T)
    include Hashable.Make_plain(T)
  end

  module _ : Regalloc_intf.Variable_name = Variable_name

  module Opcode = struct

    module Operation = struct

      type cmm_integer_comparison = Cmm.integer_comparison =
        | Ceq | Cne | Clt | Cgt | Cle | Cge
      [@@deriving sexp]

      type integer_comparison = Mach.integer_comparison =
          Isigned of cmm_integer_comparison
        | Iunsigned of cmm_integer_comparison
      [@@deriving sexp]

      type integer_operation = Mach.integer_operation =
          Iadd | Isub | Imul | Imulh | Idiv | Imod
        | Iand | Ior | Ixor | Ilsl | Ilsr | Iasr
        | Icomp of integer_comparison
        | Icheckbound
      [@@deriving sexp]

      type float_comparison = Cmm.float_comparison =
        | CFeq | CFneq | CFlt | CFnlt | CFgt | CFngt | CFle | CFnle | CFge | CFnge
      [@@deriving sexp]

      type test = Mach.test =
          Itruetest
        | Ifalsetest
        | Iinttest of integer_comparison
        | Iinttest_imm of integer_comparison * int
        | Ifloattest of float_comparison
        | Ioddtest
        | Ieventest
      [@@deriving sexp_of]

      type t = (Arch.addressing_mode, Arch.specific_operation) Mach.operation

    end

    type t =
      | Iend
      | Iop of Operation.t
      | Ireturn
      | Ififthenelse of Mach.test
      | Iswitch
      | Icatch of Cmm.rec_flag * int list
      | Iexit of int
      | Itrywith
      | Iraise of Lambda.raise_kind

    (*
    let to_string t = Sexp.to_string ([%sexp_of: t] t)
       *)

    let to_string _ = assert false
  end

  module Instruction_metadata = struct
    module Physical_register = Physical_register
    module Constraint = Regalloc.Make_constraint(Physical_register)

    type t = 
      { name : string
      ; arguments_in : Physical_register.Kind.t array
      ; arguments_out : Physical_register.Kind.t array
      ; temporaries : Physical_register.Kind.t array
      ; constraints : Constraint.t array
      ; soft_constraints : Constraint.Soft.t array
      ; destroys : Physical_register.Set.t
      } [@@deriving fields]
  end

  module _ : Regalloc_intf.Instruction_metadata = Instruction_metadata

  module Instruction = struct
    module Physical_register = Physical_register
    module Metadata = Instruction_metadata

    type t =
      { opcode : Opcode.t
      ; metadata : Metadata.t
      } [@@deriving fields]

    (*
    let sexp_of_t t = [%sexp_of: Opcode.t] t.opcode
       *)

    let sexp_of_t _ = assert false

    let create_move ty0 ty1 =
      let opcode = Opcode.Iop Imove in
      let soft_constraints =
        if Physical_register.Kind.equal ty0 ty1 
        then [| { Metadata.Constraint.Soft.
                  base = Same 
                      ({ kind = Input; index = 0}, { kind = Output; index = 0 }) 
                ; reward = [ 1, Move ]
                ; negate = false
                }
        |]
        else [||]
      in
      { opcode
      ; metadata = 
          { name = Opcode.to_string opcode
          ; arguments_in = [| ty0 |]
          ; arguments_out = [| ty1 |]
          ; temporaries = [||]
          ; constraints = [||]
          ; soft_constraints
          ; destroys = Physical_register.Set.empty
          }
      }

  end

  module _ : Regalloc_intf.Instruction = Instruction

end

let%expect_test "amd64" =
  let module R = Make((val Asmcomp_platform.platform Amd64)) in
  R.Physical_register_kind.all
  |> [%sexp_of: R.Physical_register_kind.t list]
  |> print_s
  ;
  [%expect {| (ValAddrInt Float) |}];
  R.Physical_register.all_by_kind
  |> [%sexp_of: R.Physical_register.Set.t R.Physical_register_kind.Map.t]
  |> print_s
  ;
  ();
  [%expect {|
    ((ValAddrInt
      (%rax %rbx %rdi %rsi %rdx %rcx %r8 %r9 %r12 %r13 %r10 %r11 %rbp))
     (Float
      (%xmm0 %xmm1 %xmm2 %xmm3 %xmm4 %xmm5 %xmm6 %xmm7 %xmm8 %xmm9 %xmm10 %xmm11
       %xmm12 %xmm13 %xmm14 %xmm15))) |}];
  let module A = Regalloc.Make_allocator(R.Variable_name)(R.Instruction) in
  ()
