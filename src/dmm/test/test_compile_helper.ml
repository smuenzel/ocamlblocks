open! Core
open! Blocks_dmm

let rec clean_sexp = function
  | Sexp.Atom _ as s -> Some s
  | Sexp.List [] -> None
  | Sexp.List l ->
    match List.filter_map ~f:clean_sexp l with
    | [] -> None
    | list -> Some (Sexp.List list)

let clean_sexp s =
  clean_sexp s
  |> Option.value ~default:(Sexp.List [])

let print_s s =
  print_s (clean_sexp s)

let%expect_test "" =
  let t =
    Compile_helper.compile_structure
      {|
   let myfunction z () =
      try
        let x, y =
          match z with
          | 0 -> 0, (z - 1)
          | 1 -> 122, 0
          | _ -> assert false
        in
      Some (x + y)  
      with
      | Assert_failure _ -> None
    |}
  in
  let filtered_cmm =
    t.cmm
    |> List.filter ~f:(function
        | Cdata _ -> false
        | _ -> true
      )
  in
  filtered_cmm
  |> [%sexp_of: Ocamlc_kit.Cmm.phrase list]
  |> print_s
  ;
  [%expect {|
    ((Cfunction
      ((fun_name camlTest.myfunction_10)
       (fun_args
        (((Without_provenance (Local (name z) (stamp 48))) (Val))
         ((Without_provenance (Local (name param) (stamp 47))) (Val))))
       (fun_body
        (Ctrywith
         (Ccatch Nonrecursive
          ((8
            (((Without_provenance (Local (name x) (stamp 58))) (Val))
             ((Without_provenance (Local (name y) (stamp 57))) (Val)))
            (Cop Calloc
             ((Cconst_natint 1024)
              (Cop Caddi
               ((Cop Caddi
                 ((Cvar (Local (name x) (stamp 58)))
                  (Cvar (Local (name y) (stamp 57)))))
                (Cconst_int -1)))))))
          (Cifthenelse
           (Cop (Ccmpi Cne) ((Cvar (Local (name z) (stamp 48))) (Cconst_int 1)))
           (Cifthenelse
            (Cop (Ccmpi Cne) ((Cvar (Local (name z) (stamp 48))) (Cconst_int 3)))
            (Cop (Craise Raise_notrace)
             ((Cconst_symbol camlTest__Pmakeblock_60)))
            (Cexit 8 ((Cconst_int 245) (Cconst_int 1))))
           (Cexit 8
            ((Cconst_int 1)
             (Cop Caddi ((Cvar (Local (name z) (stamp 48))) (Cconst_int -2)))))))
         (Without_provenance (Local (name exn) (stamp 50)))
         (Cifthenelse
          (Cop (Ccmpi Ceq)
           ((Cop
             (Cload (memory_chunk Word_val) (mutability Mutable)
              (is_atomic false))
             ((Cvar (Local (name exn) (stamp 50)))))
            (Cconst_symbol caml_exn_Assert_failure)))
          (Cconst_int 1)
          (Cop (Craise Raise_notrace) ((Cvar (Local (name exn) (stamp 50))))))))
       (fun_codegen_options) (fun_poll Default_poll) (fun_dbg)))
     (Cfunction
      ((fun_name camlTest.entry) (fun_args) (fun_body (Cconst_int 1))
       (fun_codegen_options (Reduce_code_size No_CSE)) (fun_poll Default_poll)
       (fun_dbg)))) |}];
  let tcmm =
    List.filter_map filtered_cmm
      ~f:(function 
          | Cdata _ -> None
          | Cfunction f ->
            Tcmm.type_function
              ~fun_args:f.fun_args
              f.fun_body
            |> Some
        )
  in
  tcmm
  |> [%sexp_of: Tcmm.Texpr.t list]
  |> print_s;
  [%expect {|
    (((Ctrywith
       ((Ccatch Nonrecursive
         ((8 (((Var x_58) (Val)) ((Var y_57) (Val)))
           ((Cop Calloc
             (((Cconst_natint 1024) (Int))
              ((Cop Caddi
                (((Cop Caddi
                   (((Cvar (Var x_58)) (Val)) ((Cvar (Var y_57)) (Val))))
                  (Int))
                 ((Cconst_int -1) (Int))))
               (Int))))
            (Val))))
         ((Cifthenelse
           ((Cop (Ccmpi Cne) (((Cvar (Var z_48)) (Val)) ((Cconst_int 1) (Int))))
            (Int))
           ((Cifthenelse
             ((Cop (Ccmpi Cne)
               (((Cvar (Var z_48)) (Val)) ((Cconst_int 3) (Int))))
              (Int))
             ((Cop (Craise Raise_notrace)
               (((Cconst_symbol camlTest__Pmakeblock_60) (Int))))
              (Val))
             ((Cexit 8 (((Cconst_int 245) (Int)) ((Cconst_int 1) (Int)))) (Val)))
            (Val))
           ((Cexit 8
             (((Cconst_int 1) (Int))
              ((Cop Caddi (((Cvar (Var z_48)) (Val)) ((Cconst_int -2) (Int))))
               (Int))))
            (Val)))
          (Val)))
        (Val))
       (Var exn_50)
       ((Cifthenelse
         ((Cop (Ccmpi Ceq)
           (((Cop
              (Cload (memory_chunk Word_val) (mutability Mutable)
               (is_atomic false))
              (((Cvar (Var exn_50)))))
             (Val))
            ((Cconst_symbol caml_exn_Assert_failure) (Int))))
          (Int))
         ((Cconst_int 1) (Val))
         ((Cop (Craise Raise_notrace) (((Cvar (Var exn_50))))) (Val)))
        (Val)))
      (Val))
     ((Cconst_int 1) (Int))) |}];
  let graphs =
    List.map tcmm
      ~f:(fun tcmm ->
          let graph = Igraph_builder.create () in
          Tcmm_to_dmm.transl
            graph
            tcmm
            ~this_id:Dmm_intf.Node_id.enter
            ~fallthrough_id:Dmm_intf.Node_id.exit
            Int.Map.empty
            ~trap_stack:[]
            ~trap_handlers:Tcmm_to_dmm.Trap_stack.Map.empty
            ~result:(Some (Var (Dmm_intf.Backend_var.create_local "output")))
          ;
          graph
        )
  in
  graphs
  |> [%sexp_of: Dmm_intf.Inst_args.t Igraph_builder.t list]
  |> print_s
  ;
  ();
  [%expect {|
    (((current_node_id 40) (current_var_id 13)
      (temp_vars
       (((Temp 0) (Int)) ((Temp 1) (Int)) ((Temp 2) (Int)) ((Temp 3) (Int))
        ((Temp 4) (Int)) ((Temp 5) (Int)) ((Temp 6) (Int)) ((Temp 7) (Int))
        ((Temp 8) (Int)) ((Temp 9) (Int)) ((Temp 10) (Int)) ((Temp 11) (Val))
        ((Temp 12) (Int))))
      (graph
       (((node_id 2) (next (9))
         (c
          ((inst (Pure (I (Const 1)))) (inputs) (output ((Temp 1)))
           (trap_stack (0)))))
        ((node_id 9) (next (8))
         (c ((inst Nop) (inputs) (output) (trap_stack (0)))))
        ((node_id 8) (next (7))
         (c
          ((inst (Pure (I (Cmp (signed true) (comparison Cne)))))
           (inputs ((Var z_48) (Temp 1))) (output ((Temp 0))) (trap_stack (0)))))
        ((node_id 7) (next (10 11))
         (c
          ((inst (Flow (Test_and_branch (Bool (then_value true)))))
           (inputs ((Temp 0))) (output) (trap_stack (0)))))
        ((node_id 11) (next (21))
         (c
          ((inst (Pure (I (Const 1)))) (inputs) (output ((Var x_58)))
           (trap_stack (0)))))
        ((node_id 10) (next (14))
         (c
          ((inst (Pure (I (Const 3)))) (inputs) (output ((Temp 3)))
           (trap_stack (0)))))
        ((node_id 21) (next (24))
         (c
          ((inst (Pure (I (Const -2)))) (inputs) (output ((Temp 5)))
           (trap_stack (0)))))
        ((node_id 14) (next (13))
         (c ((inst Nop) (inputs) (output) (trap_stack (0)))))
        ((node_id 24) (next (23))
         (c ((inst Nop) (inputs) (output) (trap_stack (0)))))
        ((node_id 13) (next (12))
         (c
          ((inst (Pure (I (Cmp (signed true) (comparison Cne)))))
           (inputs ((Var z_48) (Temp 3))) (output ((Temp 2))) (trap_stack (0)))))
        ((node_id 23) (next (22))
         (c
          ((inst (Pure (I Add))) (inputs ((Var z_48) (Temp 5)))
           (output ((Var y_57))) (trap_stack (0)))))
        ((node_id 12) (next (15 16))
         (c
          ((inst (Flow (Test_and_branch (Bool (then_value true)))))
           (inputs ((Temp 2))) (output) (trap_stack (0)))))
        ((node_id 22) (next (6))
         (c ((inst Nop) (inputs) (output) (trap_stack (0)))))
        ((node_id 16) (next (19))
         (c
          ((inst (Pure (I (Const 245)))) (inputs) (output ((Var x_58)))
           (trap_stack (0)))))
        ((node_id 15) (next (18))
         (c
          ((inst (Pure (Symbol camlTest__Pmakeblock_60))) (inputs)
           (output ((Temp 4))) (trap_stack (0)))))
        ((node_id 19) (next (20))
         (c
          ((inst (Pure (I (Const 1)))) (inputs) (output ((Var y_57)))
           (trap_stack (0)))))
        ((node_id 18) (next (17))
         (c ((inst Nop) (inputs) (output) (trap_stack (0)))))
        ((node_id 20) (next (6))
         (c ((inst Nop) (inputs) (output) (trap_stack (0)))))
        ((node_id 17) (next (4))
         (c
          ((inst (Flow (Raise (kind Raise_notrace) (local true))))
           (inputs ((Temp 4))) (output ((Var output_70))) (trap_stack (0)))))
        ((node_id 6) (next (26))
         (c
          ((inst (Pure (I (Const 1024)))) (inputs) (output ((Temp 6)))
           (trap_stack (0)))))
        ((node_id 4) (next (5))
         (c ((inst Nop) (inputs) (output) (trap_stack (0)))))
        ((node_id 26) (next (30))
         (c ((inst Nop) (inputs) (output) (trap_stack (0)))))
        ((node_id 5) (next (35)) (c ((inst Nop) (inputs) (output) (trap_stack))))
        ((node_id 30) (next (29))
         (c
          ((inst (Pure (I Add))) (inputs ((Var x_58) (Var y_57)))
           (output ((Temp 8))) (trap_stack (0)))))
        ((node_id 35) (next (34))
         (c
          ((inst
            (Mem
             (Load (memory_chunk Word_val) (mutability Mutable)
              (is_atomic false))))
           (inputs ((Var exn_50))) (output ((Temp 11))) (trap_stack))))
        ((node_id 29) (next (31))
         (c
          ((inst (Pure (I (Const -1)))) (inputs) (output ((Temp 9)))
           (trap_stack (0)))))
        ((node_id 34) (next (36))
         (c
          ((inst (Pure (Symbol caml_exn_Assert_failure))) (inputs)
           (output ((Temp 12))) (trap_stack))))
        ((node_id 31) (next (28))
         (c ((inst Nop) (inputs) (output) (trap_stack (0)))))
        ((node_id 36) (next (33))
         (c ((inst Nop) (inputs) (output) (trap_stack))))
        ((node_id 28) (next (27))
         (c
          ((inst (Pure (I Add))) (inputs ((Temp 8) (Temp 9))) (output ((Temp 7)))
           (trap_stack (0)))))
        ((node_id 33) (next (32))
         (c
          ((inst (Pure (I (Cmp (signed true) (comparison Ceq)))))
           (inputs ((Temp 11) (Temp 12))) (output ((Temp 10))) (trap_stack))))
        ((node_id 27) (next (25))
         (c ((inst Nop) (inputs) (output) (trap_stack (0)))))
        ((node_id 32) (next (37 38))
         (c
          ((inst (Flow (Test_and_branch (Bool (then_value true)))))
           (inputs ((Temp 10))) (output) (trap_stack))))
        ((node_id 25) (next (3))
         (c
          ((inst (Mem Alloc)) (inputs ((Temp 6) (Temp 7)))
           (output ((Var output_70))) (trap_stack (0)))))
        ((node_id 38) (next (39))
         (c ((inst Nop) (inputs) (output) (trap_stack))))
        ((node_id 37) (next (0))
         (c
          ((inst (Pure (I (Const 1)))) (inputs) (output ((Var output_70)))
           (trap_stack))))
        ((node_id 3) (next (0)) (c ((inst Nop) (inputs) (output) (trap_stack))))
        ((node_id 39) (next (1))
         (c
          ((inst (Flow (Raise (kind Raise_notrace) (local false))))
           (inputs ((Var exn_50))) (output ((Var output_70))) (trap_stack)))))))
     ((current_node_id 3) (current_var_id 0) (temp_vars)
      (graph
       (((node_id 2) (next (0))
         (c
          ((inst (Pure (I (Const 1)))) (inputs) (output ((Var output_71)))
           (trap_stack)))))))) |}];
  let dot_f ~inst ~inputs ~output x =
    let i_sexp =
      let f = Format.str_formatter in
      Format.pp_set_margin f 20;
      Sexp.pp_hum f ([%sexp_of: Dmm_intf.Dinst.t] (inst x));
      Format.flush_str_formatter ()
      |> String.substr_replace_all ~pattern:"\n" ~with_:"\\n"
    in
    let inputs =
      Array.to_list (inputs x)
      |> List.map ~f:(Printf.sprintf !"i:%{sexp:Dmm_intf.Dvar.t}")
    in
    let output =
      match output x with
      | None -> []
      | Some output ->
        [ Printf.sprintf !"o:%{sexp:Dmm_intf.Dvar.t}" output ]
    in
    String.concat
      ~sep:"\\n"
      (List.concat [ [ i_sexp ] ; inputs; output ] )

  in
  List.iter graphs
    ~f:(fun g ->
      Igraph_builder.to_dot g
        ~f:(Dmm_intf.Inst_args.(dot_f ~inst ~inputs ~output))
      |> Compile_helper.run_graph_easy
      |> print_endline
    );
  [%expect {|
                                                         ┌───────────────────────────┐
                                                         │           (Pure           │
                                                         │      (I (Const 1)))       │
                                                         │        o:(Temp 1)         │
                                                         └───────────────────────────┘
                                                           │
                                                           │
                                                           ▼
                                                         ┌───────────────────────────┐
                                                         │            Nop            │
                                                         └───────────────────────────┘
                                                           │
                                                           │
                                                           ▼
                                                         ┌───────────────────────────┐
                                                         │           (Pure           │
                                                         │            (I             │
                                                         │           (Cmp            │
                                                         │       (signed true)       │
                                                         │    (comparison Cne))))    │
                                                         │       i:(Var z_48)        │
                                                         │        i:(Temp 1)         │
                                                         │        o:(Temp 0)         │
                                                         └───────────────────────────┘
                                                           │
                                                           │
                                                           ▼
                              ┌───────────────────┐      ┌───────────────────────────┐
                              │                   │      │           (Flow           │
                              │       (Pure       │      │     (Test_and_branch      │
                              │  (I (Const 1)))   │      │           (Bool           │
                              │   o:(Var x_58)    │      │        (then_value        │
                              │                   │  1   │         true))))          │
                              │                   │ ◀─── │        i:(Temp 0)         │
                              └───────────────────┘      └───────────────────────────┘
                                │                          │
                                │                          │ 0
                                ▼                          ▼
                              ┌───────────────────┐      ┌───────────────────────────┐
                              │       (Pure       │      │           (Pure           │
                              │  (I (Const -2)))  │      │      (I (Const 3)))       │
                              │    o:(Temp 5)     │      │        o:(Temp 3)         │
                              └───────────────────┘      └───────────────────────────┘
                                │                          │
                                │                          │
                                ▼                          ▼
                              ┌───────────────────┐      ┌───────────────────────────┐
                              │        Nop        │      │            Nop            │
                              └───────────────────┘      └───────────────────────────┘
                                │                          │
                                │                          │
                                ▼                          ▼
                              ┌───────────────────┐      ┌───────────────────────────┐
                              │                   │      │           (Pure           │
                              │                   │      │            (I             │
                              │  (Pure (I Add))   │      │           (Cmp            │
                              │   i:(Var z_48)    │      │       (signed true)       │
                              │    i:(Temp 5)     │      │    (comparison Cne))))    │
                              │   o:(Var y_57)    │      │       i:(Var z_48)        │
                              │                   │      │        i:(Temp 3)         │
                              │                   │      │        o:(Temp 2)         │
                              └───────────────────┘      └───────────────────────────┘
                                │                          │
                                │                          │
                                ▼                          ▼
                              ┌───────────────────┐      ┌───────────────────────────┐      ┌──────────────────┐
                              │                   │      │           (Flow           │      │                  │
                              │                   │      │     (Test_and_branch      │      │      (Pure       │
                              │        Nop        │      │           (Bool           │      │ (I (Const 245))) │
                              │                   │      │        (then_value        │      │   o:(Var x_58)   │
                              │                   │      │         true))))          │  1   │                  │
                              │                   │      │        i:(Temp 2)         │ ───▶ │                  │
                              └───────────────────┘      └───────────────────────────┘      └──────────────────┘
                                │                          │                                  │
                                │                          │ 0                                │
                                ▼                          ▼                                  ▼
                              ┌───────────────────┐      ┌───────────────────────────┐      ┌──────────────────┐
                              │       (Pure       │      │           (Pure           │      │      (Pure       │
                              │ (I (Const 1024))) │      │          (Symbol          │      │  (I (Const 1)))  │
                              │    o:(Temp 6)     │      │ camlTest__Pmakeblock_60)) │      │   o:(Var y_57)   │
                              │                   │ ◀┐   │        o:(Temp 4)         │      │                  │
                              └───────────────────┘  │   └───────────────────────────┘      └──────────────────┘
                                │                    │     │                                  │
                                │                    │     │                                  │
                                ▼                    │     ▼                                  ▼
                              ┌───────────────────┐  │   ┌───────────────────────────┐      ┌──────────────────┐
                              │        Nop        │  │   │            Nop            │      │       Nop        │
                              └───────────────────┘  │   └───────────────────────────┘      └──────────────────┘
                                │                    │     │                                  │
                                │                    │     │                                  │
                                ▼                    │     ▼                                  │
                              ┌───────────────────┐  │   ┌───────────────────────────┐        │
                              │                   │  │   │           (Flow           │        │
                              │  (Pure (I Add))   │  │   │          (Raise           │        │
                              │   i:(Var x_58)    │  │   │           (kind           │        │
                              │   i:(Var y_57)    │  │   │      Raise_notrace)       │        │
                              │    o:(Temp 8)     │  │   │      (local true)))       │        │
                              │                   │  │   │        i:(Temp 4)         │        │
                              │                   │  │   │     o:(Var output_70)     │        │
                              └───────────────────┘  │   └───────────────────────────┘        │
                                │                    │     │                                  │
                                │                    │     │                                  │
                                ▼                    │     ▼                                  │
                              ┌───────────────────┐  │   ┌───────────────────────────┐        │
                              │       (Pure       │  │   │                           │        │
                              │  (I (Const -1)))  │  │   │            Nop            │        │
                              │    o:(Temp 9)     │  │   │                           │        │
                              └───────────────────┘  │   └───────────────────────────┘        │
                                │                    │     │                                  │
                                │                    │     │                                  │
                                ▼                    │     ▼                                  │
                              ┌───────────────────┐  │   ┌───────────────────────────┐        │
                              │        Nop        │  │   │            Nop            │        │
                              └───────────────────┘  │   └───────────────────────────┘        │
                                │                    │     │                                  │
                                │                    │     │                                  │
                                ▼                    │     ▼                                  │
                              ┌───────────────────┐  │   ┌───────────────────────────┐        │
                              │                   │  │   │           (Mem            │        │
                              │                   │  │   │           (Load           │        │
                              │  (Pure (I Add))   │  │   │       (memory_chunk       │        │
                              │    i:(Temp 8)     │  │   │         Word_val)         │        │
                              │    i:(Temp 9)     │  │   │        (mutability        │        │
                              │    o:(Temp 7)     │  │   │         Mutable)          │        │
                              │                   │  │   │    (is_atomic false)))    │        │
                              │                   │  │   │      i:(Var exn_50)       │        │
                              │                   │  │   │        o:(Temp 11)        │        │
                              └───────────────────┘  │   └───────────────────────────┘        │
                                │                    │     │                                  │
                                │                    │     │                                  │
                                ▼                    │     ▼                                  │
                              ┌───────────────────┐  │   ┌───────────────────────────┐        │
                              │                   │  │   │           (Pure           │        │
                              │        Nop        │  │   │          (Symbol          │        │
                              │                   │  │   │ caml_exn_Assert_failure)) │        │
                              │                   │  │   │        o:(Temp 12)        │        │
                              └───────────────────┘  │   └───────────────────────────┘        │
                                │                    │     │                                  │
                                │                    │     │                                  │
                                ▼                    │     ▼                                  │
                              ┌───────────────────┐  │   ┌───────────────────────────┐        │
                              │    (Mem Alloc)    │  │   │                           │        │
                              │    i:(Temp 6)     │  │   │            Nop            │        │
                              │    i:(Temp 7)     │  │   │                           │        │
                              │ o:(Var output_70) │  │   │                           │        │
                              └───────────────────┘  │   └───────────────────────────┘        │
                                │                    │     │                                  │
                                │                    │     │                                  │
                                ▼                    │     ▼                                  │
                              ┌───────────────────┐  │   ┌───────────────────────────┐        │
                              │                   │  │   │           (Pure           │        │
                              │                   │  │   │            (I             │        │
                              │                   │  │   │           (Cmp            │        │
                              │        Nop        │  │   │       (signed true)       │        │
                              │                   │  │   │    (comparison Ceq))))    │        │
                              │                   │  │   │        i:(Temp 11)        │        │
                              │                   │  │   │        i:(Temp 12)        │        │
                              │                   │  │   │        o:(Temp 10)        │        │
                              └───────────────────┘  │   └───────────────────────────┘        │
                                │                    │     │                                  │
                                │                    │     │                                  │
                                ▼                    │     ▼                                  │
    ┌───────────────────┐     ┌───────────────────┐  │   ┌───────────────────────────┐        │
    │                   │     │                   │  │   │           (Flow           │        │
    │       (Pure       │     │                   │  │   │     (Test_and_branch      │        │
    │  (I (Const 1)))   │     │      <EXIT>       │  │   │           (Bool           │        │
    │ o:(Var output_70) │     │                   │  │   │        (then_value        │        │
    │                   │     │                   │  │   │         true))))          │        │
    │                   │ ──▶ │                   │  │   │        i:(Temp 10)        │ ─┐     │
    └───────────────────┘     └───────────────────┘  │   └───────────────────────────┘  │     │
      ▲                                              │     │                            │     │
      │ 0                                            │     │ 1                          │     │
      │                                              │     ▼                            │     │
      │                                              │   ┌───────────────────────────┐  │     │
      │                                              │   │            Nop            │  │     │
      │                                              │   └───────────────────────────┘  │     │
      │                                              │     │                            │     │
      │                                              │     │                            │     │
      │                                              │     ▼                            │     │
      │                                              │   ┌───────────────────────────┐  │     │
      │                                              │   │           (Flow           │  │     │
      │                                              │   │          (Raise           │  │     │
      │                                              │   │           (kind           │  │     │
      │                                              │   │      Raise_notrace)       │  │     │
      │                                              │   │      (local false)))      │  │     │
      │                                              │   │      i:(Var exn_50)       │  │     │
      │                                              │   │     o:(Var output_70)     │  │     │
      │                                              │   └───────────────────────────┘  │     │
      │                                              │     │                            │     │
      │                                              │     │                            │     │
      │                                              │     ▼                            │     │
      │                                              │   ┌───────────────────────────┐  │     │
      │                                              │   │          <RAISE>          │  │     │
      │                                              │   └───────────────────────────┘  │     │
      │                                              │                                  │     │
      │                                              └──────────────────────────────────┼─────┘
      │                                                                                 │
      │                                                                                 │
      └─────────────────────────────────────────────────────────────────────────────────┘

    ┌───────────────────┐
    │      <RAISE>      │
    └───────────────────┘
    ┌───────────────────┐
    │       (Pure       │
    │  (I (Const 1)))   │
    │ o:(Var output_71) │
    └───────────────────┘
      │
      │
      ▼
    ┌───────────────────┐
    │      <EXIT>       │
    └───────────────────┘ |}];
  let graphs_notrap = List.map graphs ~f:Dmm_remove_trap.remove_trap in
  List.iter graphs_notrap
    ~f:(fun g ->
      Igraph_builder.to_dot g
        ~f:(Dmm_intf.Inst_notrap.(dot_f ~inst ~inputs ~output))
      |> Compile_helper.run_graph_easy
      |> print_endline
    );
  [%expect {|
                                                          ┌───────────────────────────┐
                                                          │           (Pure           │
                                                          │      (I (Const 1)))       │
                                                          │        o:(Temp 1)         │
                                                          └───────────────────────────┘
                                                            │
                                                            │
                                                            ▼
                                                          ┌───────────────────────────┐
                                                          │            Nop            │
                                                          └───────────────────────────┘
                                                            │
                                                            │
                                                            ▼
                                                          ┌───────────────────────────┐
                                                          │           (Pure           │
                                                          │            (I             │
                                                          │           (Cmp            │
                                                          │       (signed true)       │
                                                          │    (comparison Cne))))    │
                                                          │       i:(Var z_48)        │
                                                          │        i:(Temp 1)         │
                                                          │        o:(Temp 0)         │
                                                          └───────────────────────────┘
                                                            │
                                                            │
                                                            ▼
                              ┌────────────────────┐      ┌───────────────────────────┐
                              │                    │      │           (Flow           │
                              │       (Pure        │      │     (Test_and_branch      │
                              │   (I (Const 1)))   │      │           (Bool           │
                              │    o:(Var x_58)    │      │        (then_value        │
                              │                    │  1   │         true))))          │
                              │                    │ ◀─── │        i:(Temp 0)         │
                              └────────────────────┘      └───────────────────────────┘
                                │                           │
                                │                           │ 0
                                ▼                           ▼
                              ┌────────────────────┐      ┌───────────────────────────┐
                              │       (Pure        │      │           (Pure           │
                              │  (I (Const -2)))   │      │      (I (Const 3)))       │
                              │     o:(Temp 5)     │      │        o:(Temp 3)         │
                              └────────────────────┘      └───────────────────────────┘
                                │                           │
                                │                           │
                                ▼                           ▼
                              ┌────────────────────┐      ┌───────────────────────────┐
                              │        Nop         │      │            Nop            │
                              └────────────────────┘      └───────────────────────────┘
                                │                           │
                                │                           │
                                ▼                           ▼
                              ┌────────────────────┐      ┌───────────────────────────┐
                              │                    │      │           (Pure           │
                              │                    │      │            (I             │
                              │   (Pure (I Add))   │      │           (Cmp            │
                              │    i:(Var z_48)    │      │       (signed true)       │
                              │     i:(Temp 5)     │      │    (comparison Cne))))    │
                              │    o:(Var y_57)    │      │       i:(Var z_48)        │
                              │                    │      │        i:(Temp 3)         │
                              │                    │      │        o:(Temp 2)         │
                              └────────────────────┘      └───────────────────────────┘
                                │                           │
                                │                           │
                                ▼                           ▼
                              ┌────────────────────┐      ┌───────────────────────────┐      ┌──────────────────┐
                              │                    │      │           (Flow           │      │                  │
                              │                    │      │     (Test_and_branch      │      │      (Pure       │
                              │        Nop         │      │           (Bool           │      │ (I (Const 245))) │
                              │                    │      │        (then_value        │      │   o:(Var x_58)   │
                              │                    │      │         true))))          │  1   │                  │
                              │                    │      │        i:(Temp 2)         │ ───▶ │                  │
                              └────────────────────┘      └───────────────────────────┘      └──────────────────┘
                                │                           │                                  │
                                │                           │ 0                                │
                                ▼                           ▼                                  ▼
                              ┌────────────────────┐      ┌───────────────────────────┐      ┌──────────────────┐
                              │       (Pure        │      │           (Pure           │      │      (Pure       │
                              │ (I (Const 1024)))  │      │          (Symbol          │      │  (I (Const 1)))  │
                              │     o:(Temp 6)     │      │ camlTest__Pmakeblock_60)) │      │   o:(Var y_57)   │
                              │                    │ ◀┐   │        o:(Temp 4)         │      │                  │
                              └────────────────────┘  │   └───────────────────────────┘      └──────────────────┘
                                │                     │     │                                  │
                                │                     │     │                                  │
                                ▼                     │     ▼                                  ▼
                              ┌────────────────────┐  │   ┌───────────────────────────┐      ┌──────────────────┐
                              │        Nop         │  │   │            Nop            │      │       Nop        │
                              └────────────────────┘  │   └───────────────────────────┘      └──────────────────┘
                                │                     │     │                                  │
                                │                     │     │                                  │
                                ▼                     │     ▼                                  │
                              ┌────────────────────┐  │   ┌───────────────────────────┐        │
                              │                    │  │   │           (Flow           │        │
                              │   (Pure (I Add))   │  │   │          (Raise           │        │
                              │    i:(Var x_58)    │  │   │           (kind           │        │
                              │    i:(Var y_57)    │  │   │      Raise_notrace)       │        │
                              │     o:(Temp 8)     │  │   │      (local true)))       │        │
                              │                    │  │   │        i:(Temp 4)         │        │
                              │                    │  │   │     o:(Var output_70)     │        │
                              └────────────────────┘  │   └───────────────────────────┘        │
                                │                     │     │                                  │
                                │                     │     │                                  │
                                ▼                     │     ▼                                  │
                              ┌────────────────────┐  │   ┌───────────────────────────┐        │
                              │       (Pure        │  │   │                           │        │
                              │  (I (Const -1)))   │  │   │            Nop            │        │
                              │     o:(Temp 9)     │  │   │                           │        │
                              └────────────────────┘  │   └───────────────────────────┘        │
                                │                     │     │                                  │
                                │                     │     │                                  │
                                ▼                     │     ▼                                  │
                              ┌────────────────────┐  │   ┌───────────────────────────┐        │
                              │        Nop         │  │   │           (Trap           │        │
                              │                    │  │   │    (direction Leave))     │        │
                              └────────────────────┘  │   └───────────────────────────┘        │
                                │                     │     │                                  │
                                │                     │     │                                  │
                                ▼                     │     ▼                                  │
                              ┌────────────────────┐  │   ┌───────────────────────────┐        │
                              │   (Pure (I Add))   │  │   │                           │        │
                              │     i:(Temp 8)     │  │   │            Nop            │        │
                              │     i:(Temp 9)     │  │   │                           │        │
                              │     o:(Temp 7)     │  │   │                           │        │
                              └────────────────────┘  │   └───────────────────────────┘        │
                                │                     │     │                                  │
                                │                     │     │                                  │
                                ▼                     │     ▼                                  │
                              ┌────────────────────┐  │   ┌───────────────────────────┐        │
                              │                    │  │   │           (Mem            │        │
                              │                    │  │   │           (Load           │        │
                              │                    │  │   │       (memory_chunk       │        │
                              │                    │  │   │         Word_val)         │        │
                              │        Nop         │  │   │        (mutability        │        │
                              │                    │  │   │         Mutable)          │        │
                              │                    │  │   │    (is_atomic false)))    │        │
                              │                    │  │   │      i:(Var exn_50)       │        │
                              │                    │  │   │        o:(Temp 11)        │        │
                              └────────────────────┘  │   └───────────────────────────┘        │
                                │                     │     │                                  │
                                │                     │     │                                  │
                                ▼                     │     ▼                                  │
                              ┌────────────────────┐  │   ┌───────────────────────────┐        │
                              │    (Mem Alloc)     │  │   │           (Pure           │        │
                              │     i:(Temp 6)     │  │   │          (Symbol          │        │
                              │     i:(Temp 7)     │  │   │ caml_exn_Assert_failure)) │        │
                              │ o:(Var output_70)  │  │   │        o:(Temp 12)        │        │
                              └────────────────────┘  │   └───────────────────────────┘        │
                                │                     │     │                                  │
                                │                     │     │                                  │
                                ▼                     │     ▼                                  │
                              ┌────────────────────┐  │   ┌───────────────────────────┐        │
                              │       (Trap        │  │   │            Nop            │        │
                              │ (direction Leave)) │  │   │                           │        │
                              └────────────────────┘  │   └───────────────────────────┘        │
                                │                     │     │                                  │
                                │                     │     │                                  │
                                ▼                     │     ▼                                  │
                              ┌────────────────────┐  │   ┌───────────────────────────┐        │
                              │                    │  │   │           (Pure           │        │
                              │                    │  │   │            (I             │        │
                              │                    │  │   │           (Cmp            │        │
                              │        Nop         │  │   │       (signed true)       │        │
                              │                    │  │   │    (comparison Ceq))))    │        │
                              │                    │  │   │        i:(Temp 11)        │        │
                              │                    │  │   │        i:(Temp 12)        │        │
                              │                    │  │   │        o:(Temp 10)        │        │
                              └────────────────────┘  │   └───────────────────────────┘        │
                                │                     │     │                                  │
                                │                     │     │                                  │
                                ▼                     │     ▼                                  │
    ┌───────────────────┐     ┌────────────────────┐  │   ┌───────────────────────────┐        │
    │                   │     │                    │  │   │           (Flow           │        │
    │       (Pure       │     │                    │  │   │     (Test_and_branch      │        │
    │  (I (Const 1)))   │     │       <EXIT>       │  │   │           (Bool           │        │
    │ o:(Var output_70) │     │                    │  │   │        (then_value        │        │
    │                   │     │                    │  │   │         true))))          │        │
    │                   │ ──▶ │                    │  │   │        i:(Temp 10)        │ ─┐     │
    └───────────────────┘     └────────────────────┘  │   └───────────────────────────┘  │     │
      ▲                                               │     │                            │     │
      │ 0                                             │     │ 1                          │     │
      │                                               │     ▼                            │     │
      │                                               │   ┌───────────────────────────┐  │     │
      │                                               │   │            Nop            │  │     │
      │                                               │   └───────────────────────────┘  │     │
      │                                               │     │                            │     │
      │                                               │     │                            │     │
      │                                               │     ▼                            │     │
      │                                               │   ┌───────────────────────────┐  │     │
      │                                               │   │           (Flow           │  │     │
      │                                               │   │          (Raise           │  │     │
      │                                               │   │           (kind           │  │     │
      │                                               │   │      Raise_notrace)       │  │     │
      │                                               │   │      (local false)))      │  │     │
      │                                               │   │      i:(Var exn_50)       │  │     │
      │                                               │   │     o:(Var output_70)     │  │     │
      │                                               │   └───────────────────────────┘  │     │
      │                                               │     │                            │     │
      │                                               │     │                            │     │
      │                                               │     ▼                            │     │
      │                                               │   ┌───────────────────────────┐  │     │
      │                                               │   │          <RAISE>          │  │     │
      │                                               │   └───────────────────────────┘  │     │
      │                                               │                                  │     │
      │                                               └──────────────────────────────────┼─────┘
      │                                                                                  │
      │                                                                                  │
      └──────────────────────────────────────────────────────────────────────────────────┘

    ┌───────────────────┐
    │      <RAISE>      │
    └───────────────────┘
    ┌───────────────────┐
    │       (Pure       │
    │  (I (Const 1)))   │
    │ o:(Var output_71) │
    └───────────────────┘
      │
      │
      ▼
    ┌───────────────────┐
    │      <EXIT>       │
    └───────────────────┘ |}];
  List.iter ~f:Dmm_remove_trap.remove_nop graphs_notrap;
  List.iter graphs_notrap
    ~f:(fun g ->
      Igraph_builder.to_dot g
        ~f:(Dmm_intf.Inst_notrap.(dot_f ~inst ~inputs ~output))
      |> Compile_helper.run_graph_easy
      |> print_endline
    );
  ();
  [%expect {|
                                     ┌───────────────────────────┐
                                     │           (Pure           │
                                     │      (I (Const 1)))       │
                                     │        o:(Temp 1)         │
                                     └───────────────────────────┘
                                       │
                                       │
                                       ▼
                                     ┌───────────────────────────┐
                                     │           (Pure           │
                                     │            (I             │
                                     │           (Cmp            │
                                     │       (signed true)       │
                                     │    (comparison Cne))))    │
                                     │       i:(Var z_48)        │
                                     │        i:(Temp 1)         │
                                     │        o:(Temp 0)         │
                                     └───────────────────────────┘
                                       │
                                       │
                                       ▼
         ┌────────────────────┐      ┌───────────────────────────┐
         │                    │      │           (Flow           │
         │       (Pure        │      │     (Test_and_branch      │
         │   (I (Const 1)))   │      │           (Bool           │
         │    o:(Var x_58)    │      │        (then_value        │
         │                    │  1   │         true))))          │
         │                    │ ◀─── │        i:(Temp 0)         │
         └────────────────────┘      └───────────────────────────┘
           │                           │
           │                           │ 0
           ▼                           ▼
         ┌────────────────────┐      ┌───────────────────────────┐
         │       (Pure        │      │           (Pure           │
         │  (I (Const -2)))   │      │      (I (Const 3)))       │
         │     o:(Temp 5)     │      │        o:(Temp 3)         │
         └────────────────────┘      └───────────────────────────┘
           │                           │
           │                           │
           ▼                           ▼
         ┌────────────────────┐      ┌───────────────────────────┐
         │                    │      │           (Pure           │
         │                    │      │            (I             │
         │   (Pure (I Add))   │      │           (Cmp            │
         │    i:(Var z_48)    │      │       (signed true)       │
         │     i:(Temp 5)     │      │    (comparison Cne))))    │
         │    o:(Var y_57)    │      │       i:(Var z_48)        │
         │                    │      │        i:(Temp 3)         │
         │                    │      │        o:(Temp 2)         │
         └────────────────────┘      └───────────────────────────┘
           │                           │
           │                           │
           ▼                           ▼
         ┌────────────────────┐      ┌───────────────────────────┐      ┌──────────────────┐
         │                    │      │           (Flow           │      │                  │
         │       (Pure        │      │     (Test_and_branch      │      │      (Pure       │
         │ (I (Const 1024)))  │      │           (Bool           │      │ (I (Const 245))) │
         │     o:(Temp 6)     │      │        (then_value        │      │   o:(Var x_58)   │
         │                    │      │         true))))          │  1   │                  │
      ┌▶ │                    │      │        i:(Temp 2)         │ ───▶ │                  │
      │  └────────────────────┘      └───────────────────────────┘      └──────────────────┘
      │    │                           │                                  │
      │    │                           │ 0                                │
      │    ▼                           ▼                                  ▼
      │  ┌────────────────────┐      ┌───────────────────────────┐      ┌──────────────────┐
      │  │   (Pure (I Add))   │      │           (Pure           │      │      (Pure       │
      │  │    i:(Var x_58)    │      │          (Symbol          │      │  (I (Const 1)))  │
      │  │    i:(Var y_57)    │      │ camlTest__Pmakeblock_60)) │      │   o:(Var y_57)   │
      │  │     o:(Temp 8)     │      │        o:(Temp 4)         │      │                  │
      │  └────────────────────┘      └───────────────────────────┘      └──────────────────┘
      │    │                           │                                  │
      │    │                           │                                  │
      │    ▼                           ▼                                  │
      │  ┌────────────────────┐      ┌───────────────────────────┐        │
      │  │                    │      │           (Flow           │        │
      │  │                    │      │          (Raise           │        │
      │  │       (Pure        │      │           (kind           │        │
      │  │  (I (Const -1)))   │      │      Raise_notrace)       │        │
      │  │     o:(Temp 9)     │      │      (local true)))       │        │
      │  │                    │      │        i:(Temp 4)         │        │
      │  │                    │      │     o:(Var output_70)     │        │
      │  └────────────────────┘      └───────────────────────────┘        │
      │    │                           │                                  │
      │    │                           │                                  │
      │    ▼                           ▼                                  │
      │  ┌────────────────────┐      ┌───────────────────────────┐        │
      │  │   (Pure (I Add))   │      │                           │        │
      │  │     i:(Temp 8)     │      │           (Trap           │        │
      │  │     i:(Temp 9)     │      │    (direction Leave))     │        │
      │  │     o:(Temp 7)     │      │                           │        │
      │  └────────────────────┘      └───────────────────────────┘        │
      │    │                           │                                  │
      │    │                           │                                  │
      │    ▼                           ▼                                  │
      │  ┌────────────────────┐      ┌───────────────────────────┐        │
      │  │                    │      │           (Mem            │        │
      │  │                    │      │           (Load           │        │
      │  │    (Mem Alloc)     │      │       (memory_chunk       │        │
      │  │     i:(Temp 6)     │      │         Word_val)         │        │
      │  │     i:(Temp 7)     │      │        (mutability        │        │
      │  │ o:(Var output_70)  │      │         Mutable)          │        │
      │  │                    │      │    (is_atomic false)))    │        │
      │  │                    │      │      i:(Var exn_50)       │        │
      │  │                    │      │        o:(Temp 11)        │        │
      │  └────────────────────┘      └───────────────────────────┘        │
      │    │                           │                                  │
      │    │                           │                                  │
      │    ▼                           ▼                                  │
      │  ┌────────────────────┐      ┌───────────────────────────┐        │
      │  │                    │      │           (Pure           │        │
      │  │       (Trap        │      │          (Symbol          │        │
      │  │ (direction Leave)) │      │ caml_exn_Assert_failure)) │        │
      │  │                    │      │        o:(Temp 12)        │        │
      │  └────────────────────┘      └───────────────────────────┘        │
      │    │                           │                                  │
      │    │                           │                                  │
      │    │                           ▼                                  │
      │    │                         ┌───────────────────────────┐        │
      │    │                         │           (Pure           │        │
      │    │                         │            (I             │        │
      │    │                         │           (Cmp            │        │
      │    │                         │       (signed true)       │        │
      │    │                         │    (comparison Ceq))))    │        │
      │    │                         │        i:(Temp 11)        │        │
      │    │                         │        i:(Temp 12)        │        │
      │    │                         │        o:(Temp 10)        │        │
      │    │                         └───────────────────────────┘        │
      │    │                           │                                  │
      │    │                           │                                  │
      │    │                           ▼                                  │
      │    │                         ┌───────────────────────────┐        │                       ┌───────────────────┐
      │    │                         │           (Flow           │        │                       │       (Flow       │
      │    │                         │     (Test_and_branch      │        │                       │      (Raise       │
      │    │                         │           (Bool           │        │                       │       (kind       │
      │    │                         │        (then_value        │        │                       │  Raise_notrace)   │
      │    │                         │         true))))          │        │                       │  (local false)))  │
      │    │                         │        i:(Temp 10)        │        │                  1    │  i:(Var exn_50)   │
      │    │                         │                           │ ───────┼─────────────────────▶ │ o:(Var output_70) │
      │    │                         └───────────────────────────┘        │                       └───────────────────┘
      │    │                           │                                  │                         │
      │    │                           │ 0                                │                         │
      │    │                           ▼                                  │                         ▼
      │    │                         ┌───────────────────────────┐        │                       ┌───────────────────┐
      │    │                         │           (Pure           │        │                       │                   │
      │    │                         │      (I (Const 1)))       │        │                       │      <RAISE>      │
      │    │                         │     o:(Var output_70)     │        │                       │                   │
      │    │                         └───────────────────────────┘        │                       └───────────────────┘
      │    │                           │                                  │
      │    │                           │                                  │
      │    │                           ▼                                  │
      │    │                         ┌───────────────────────────┐        │
      │    └───────────────────────▶ │          <EXIT>           │        │
      │                              └───────────────────────────┘        │
      │                                                                   │
      └───────────────────────────────────────────────────────────────────┘

    ┌───────────────────┐
    │      <RAISE>      │
    └───────────────────┘
    ┌───────────────────┐
    │       (Pure       │
    │  (I (Const 1)))   │
    │ o:(Var output_71) │
    └───────────────────┘
      │
      │
      ▼
    ┌───────────────────┐
    │      <EXIT>       │
    └───────────────────┘ |}]
