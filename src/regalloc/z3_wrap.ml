open! Core
open! Z3

module Config = struct
  type t =
    { model : bool
    ; proof : bool
    } 

  let default =
    { model = true
    ; proof = false
    }

  let to_param
      { model
      ; proof
      } =
    [ "model", Bool.to_string model
    ; "proof", Bool.to_string proof
    ]

end

module Expr = Z3i.Expr

class model model =
  let open Z3i.Model in
  object(self)
    val model = model

    method eval_exn expr =
      Option.value_exn (eval model expr ~apply_model_completion:true)

    method const_e_exn expr =
      self#eval_exn expr
      (* CR smuenzel: figure out why this sometimes doesn't work *)
        (*
      Option.value_exn (get_const_interp_e model expr)
           *)
  end

module Solver_result = struct
  module Generic = Z3i.Solver_result

  type t = (model [@sexp.opaque]) Generic.t [@@deriving sexp_of]

  let model_exn = Generic.satisfiable_exn
end

class optimizer_goal handle =
  object
    method lower = Z3i.Optimize.Goal.lower handle
    method upper = Z3i.Optimize.Goal.upper handle
  end

class optimizer z3 =
  let open Z3i.Optimize in 
  let opt = create z3#ctx in
  object
    method add_list list = add_list opt list
    method add single = add opt single

    method add_soft ~weight single =
      let handle = add_soft opt single ~weight z3#symbol in
      new optimizer_goal handle

    method check what =
      check_and_get_model opt what
      |> Solver_result.Generic.map ~f:(new model)

    method check_current : Solver_result.t =
      check_current_and_get_model opt
      |> Solver_result.Generic.map ~f:(new model)

    method push = push opt
    method pop scopes = pop opt scopes 

    method to_string = to_string opt
  end

class solver z3 = 
  let open Solver in
  let solver = mk_solver z3#ctx None in
  object(self)
    method add_list list = add solver list
    method add single = self#add_list [ single ]

    method check what : Solver_result.t =
      match check solver what with
      | UNSATISFIABLE -> Unsatisfiable
      | UNKNOWN -> Unknown (get_reason_unknown solver)
      | SATISFIABLE ->
        let model = Option.value_exn (get_model solver) in
        Satisfiable (new model model)

    method check_current =
      self#check [ ]

    method push = push solver
    method pop scopes = pop solver scopes
  end

class z3 ?(config = Config.default) () =
  let ctx = mk_context (Config.to_param config) in
  let symbol_factory =
    object(self)
      val mutable symbol_count = 0

      method symbol =
        symbol_count <- symbol_count + 1;
        Symbol.mk_int ctx symbol_count

      method const sort =
        Expr.mk_const ctx self#symbol sort
    end
  in
  let rec bv =
    lazy begin
      let open BitVector in
      object(self)
        method ctx = ctx 

        val sort_mem = Memo.of_comparable (module Int) (mk_sort ctx)
        method sort length = sort_mem length

        method const length = symbol_factory#const (self#sort length)

        method size_e a = get_size (Expr.sort a)
        method add a b = mk_add ctx a b
        method sub a b = mk_sub ctx a b
        method mul a b = mk_mul ctx a b

        method and_ a b = mk_and ctx a b
        method or_ a b = mk_or ctx a b
        method xor a b = mk_xor ctx a b
        method not a = mk_not ctx a

        method shr a b = mk_lshr ctx a b

        method no_overflow (kind : [ `Unsigned | `Signed ]) a b =
          mk_add_no_overflow ctx a b (match kind with `Unsigned -> false | `Signed -> true)

        method extract a ~high ~low =
          mk_extract ctx high low a

        method extract_single a ~bit =
          self#extract a ~high:bit ~low:bit

        method sign a =
          let size = get_size (Expr.sort a) in
          self#extract_single a ~bit:(size - 1)

        method num a i =
          let sort = Expr.sort a in
          Expr.mk_numeral_int ctx i sort

        method num_s sort i =
          Expr.mk_numeral_int ctx i sort

        method num_bool bools =
          Z3i.Bitvector.Numeral.bool ctx bools

        method num_zero a = self#num a 0

        method num_zero_s s = self#num_s s 0

        method num_zero_e e = self#num_zero_s (Expr.sort e)

        method num_one_s s = self#num_s s 1

        method num_ones a =
          let sort = Expr.sort a in
          let size = get_size sort in
          let s = List.init size ~f:(Fn.const true) in
          self#num_bool s

        (* Cache these constants?? *)
        method num_repeated_bytes a b =
          let sort = Expr.sort a in
          let size = get_size sort in
          assert (size mod 8 = 0);
          mk_repeat ctx (size / 8) (Expr.mk_numeral_int ctx b (self#sort 8))

        method parity a =
          let size = get_size (Expr.sort a) in
          let current = ref (self#extract_single a ~bit:0) in
          for bit = 1 to pred size do
            let value = self#extract_single a ~bit in
            current := self#xor !current value
          done;
          !current

        method concat list =
          List.reduce_balanced_exn list
            ~f:(mk_concat ctx)

        method numeral_to_binary_array_exn e =
          Z3i.Expr.numeral_to_binary_array_exn e
      end
    end
  and bvset =
    lazy begin
      let bv = force bv in
      object(self)
        method empty length = bv#num_zero_s (bv#sort length)

        method union a b = bv#or_ a b
        method inter a b = bv#and_ a b
        method complement a = bv#not a
        method diff a b = self#inter a (self#complement b)
        method symmdiff a b = bv#xor a b

        method is_empty a =
          Boolean.mk_eq ctx a (bv#num_zero_e a)

        method is_subset a ~of_ =
          self#is_empty (self#diff a of_)

        method has_max_one_member a =
          let sort = Expr.sort a in
          let is_pow_2 =
            bv#and_
              a
              (bv#sub a (bv#num_one_s sort))
          in
          let zero = bv#num_zero_s sort in
          Boolean.mk_and ctx
            [ Boolean.mk_eq ctx is_pow_2 zero
            ]

        method has_single_member a =
          let sort = Expr.sort a in
          let is_pow_2 =
            bv#and_
              a
              (bv#sub a (bv#num_one_s sort))
          in
          let zero = bv#num_zero_s sort in
          Boolean.mk_and ctx
            [ Boolean.mk_eq ctx is_pow_2 zero
            ; Boolean.mk_not ctx (Boolean.mk_eq ctx a zero)
            ]

      end
    end
  in
  object(self)
    method ctx = ctx

    method true_ = Boolean.mk_true ctx
    method false_ = Boolean.mk_false ctx

    method symbol = symbol_factory#symbol

    method const sort = symbol_factory#const sort

    method and_ list = Boolean.mk_and ctx list
    method or_ list = Boolean.mk_or ctx list
    method xor_ list =
      List.reduce_balanced_exn list
        ~f:(Boolean.mk_xor ctx)

    method ite i t e = Boolean.mk_ite ctx i t e

    method not a = Boolean.mk_not ctx a

    method eq a b = Boolean.mk_eq ctx a b
    method neq a b = self#not (self#eq a b)
    method distinct list = Boolean.mk_distinct ctx list

    method of_blang : 't. 't Blang.t -> f:('t -> _) -> _ =
      fun (type a) (b : a Blang.t) ~(f : a -> _) ->
      match b with
      | True -> self#true_
      | False -> self#false_
      | And (a,b) -> 
        let a = self#of_blang a ~f in
        let b = self#of_blang b ~f in
        self#and_ [a; b]
      | Or (a,b) ->
        let a = self#of_blang a ~f in
        let b = self#of_blang b ~f in
        self#or_ [a; b]
      | Not a ->
        let a = self#of_blang a ~f in
        self#not a
      | If (cond, ifso, ifnot) ->
        let cond = self#of_blang cond ~f in
        let ifso = self#of_blang ifso ~f in
        let ifnot = self#of_blang ifnot ~f in
        self#ite cond ifso ifnot
      | Base b -> f b

    method bv = force bv
    method bvset = force bvset
    method solver = new solver self
    method opt = new optimizer self

    method forall 
        ?weight
        ?(patterns = [])
        ?(nopatterns = [])
        ?quantifier_id
        ?skolem_id
        ~bound_constants
        ~body
        ()
      : Quantifier.quantifier
      =
      Quantifier.mk_forall_const
        ctx
        bound_constants
        body
        weight
        patterns
        nopatterns
        quantifier_id
        skolem_id

    method forall_e 
        ?weight
        ?patterns
        ?nopatterns
        ?quantifier_id
        ?skolem_id
        ~bound_constants
        ~body
        ()
      =
      self#forall
        ?weight
        ?patterns 
        ?nopatterns 
        ?quantifier_id
        ?skolem_id
        ~bound_constants
        ~body
        ()
      |> Quantifier.expr_of_quantifier

  end

let%expect_test "" =
  let z3 = new z3 () in
  let i63 = z3#bv#sort 63 in
  let x = z3#const i63 in
  let y = z3#const i63 in
  let e = z3#eq (z3#bv#add (z3#bv#num_s i63 2) x) y in
  let solver = z3#solver in
  solver#add e;
  let result = solver#check_current in
  print_s ([%sexp_of: Solver_result.t] result);
  [%expect {| (Satisfiable <opaque>) |}];
  let model = Solver_result.model_exn result in
  print_s
    [%message "result"
        (model#const_e_exn x : Expr.t)
        (model#const_e_exn y : Expr.t)
    ];
  [%expect {|
    (result
     ("model#const_e_exn x"
      #b111111111111111111111111111111111111111111111111111111111111110)
     ("model#const_e_exn y"
      #b000000000000000000000000000000000000000000000000000000000000000)) |}]

let%expect_test "" =
  let z3 = new z3 () in
  let i63 = z3#bv#sort 63 in
  let x = z3#const i63 in
  let e = z3#bvset#has_single_member x in
  let solver = z3#solver in
  solver#add e;
  let result = solver#check_current in
  print_s ([%sexp_of: Solver_result.t] result);
  [%expect {| (Satisfiable <opaque>) |}];
  let model = Solver_result.model_exn result in
  print_s
    [%message "result"
        (model#const_e_exn x : Expr.t)
    ];
  [%expect {|
    (result
     ("model#const_e_exn x"
      #b100000000000000000000000000000000000000000000000000000000000000)) |}]

let%expect_test "" =
  let z3 = new z3 () in
  let i63 = z3#bv#sort 63 in
  let x = z3#const i63 in
  let y = z3#const i63 in
  let e = z3#bvset#is_subset x ~of_:y in
  let solver = z3#solver in
  solver#add e;
  solver#add (z3#neq y (z3#bv#num_zero y));
  solver#add (z3#neq y x);
  let result = solver#check_current in
  print_s ([%sexp_of: Solver_result.t] result);
  [%expect {| (Satisfiable <opaque>) |}];
  let model = Solver_result.model_exn result in
  print_s
    [%message "result"
        (model#const_e_exn x : Expr.t)
        (model#const_e_exn y : Expr.t)
    ];
  [%expect {|
    (result
     ("model#const_e_exn x"
      #b000000000000000000000000000000000000000000000000000000000000000)
     ("model#const_e_exn y"
      #b010011101111111111111111111111111111111111111111111111111111111)) |}]
