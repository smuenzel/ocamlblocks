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
      let x, y =
        match z with
        | 0 -> 0, (z - 1)
        | 1 -> 122, 0
        | _ -> assert false
      in
      Some (x + y)  
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
      ((fun_name camlTest.myfunction_5)
       (fun_args
        (((Without_provenance (Local (name z) (stamp 44))) (Val))
         ((Without_provenance (Local (name param) (stamp 43))) (Val))))
       (fun_body
        (Ccatch Nonrecursive
         ((7
           (((Without_provenance (Local (name x) (stamp 48))) (Val))
            ((Without_provenance (Local (name y) (stamp 47))) (Val)))
           (Cop Calloc
            ((Cconst_natint 1024)
             (Cop Caddi
              ((Cop Caddi
                ((Cvar (Local (name x) (stamp 48)))
                 (Cvar (Local (name y) (stamp 47)))))
               (Cconst_int -1)))))))
         (Cifthenelse
          (Cop (Ccmpi Cne) ((Cvar (Local (name z) (stamp 44))) (Cconst_int 1)))
          (Cifthenelse
           (Cop (Ccmpi Cne) ((Cvar (Local (name z) (stamp 44))) (Cconst_int 3)))
           (Cop (Craise Raise_notrace) ((Cconst_symbol camlTest__Pmakeblock_46)))
           (Cexit 7 ((Cconst_int 245) (Cconst_int 1))))
          (Cexit 7
           ((Cconst_int 1)
            (Cop Caddi ((Cvar (Local (name z) (stamp 44))) (Cconst_int -2))))))))
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
    (((Ccatch Nonrecursive
       ((7 (((Var x_48) (Val)) ((Var y_47) (Val)))
         ((Cop Calloc
           (((Cconst_natint 1024) (Int))
            ((Cop Caddi
              (((Cop Caddi (((Cvar (Var x_48)) (Val)) ((Cvar (Var y_47)) (Val))))
                (Int))
               ((Cconst_int -1) (Int))))
             (Int))))
          (Val))))
       ((Cifthenelse
         ((Cop (Ccmpi Cne) (((Cvar (Var z_44)) (Val)) ((Cconst_int 1) (Int))))
          (Int))
         ((Cifthenelse
           ((Cop (Ccmpi Cne) (((Cvar (Var z_44)) (Val)) ((Cconst_int 3) (Int))))
            (Int))
           ((Cop (Craise Raise_notrace)
             (((Cconst_symbol camlTest__Pmakeblock_46) (Int))))
            (Val))
           ((Cexit 7 (((Cconst_int 245) (Int)) ((Cconst_int 1) (Int)))) (Val)))
          (Val))
         ((Cexit 7
           (((Cconst_int 1) (Int))
            ((Cop Caddi (((Cvar (Var z_44)) (Val)) ((Cconst_int -2) (Int))))
             (Int))))
          (Val)))
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
            ~this_id:(Igraph_builder.enter_id graph)
            ~fallthrough_id:(Igraph_builder.exit_id graph)
            Int.Map.empty
            ~trap_stack:[]
            ~trap_handlers:Tcmm_to_dmm.Trap_stack.Map.empty
            ~result:None
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
    (((current_node_id 29) (current_var_id 10) (enter_id 2) (exit_id 0)
      (raise_id 1)
      (temp_vars
       (((Temp 0) (Int)) ((Temp 1) (Int)) ((Temp 2) (Int)) ((Temp 3) (Int))
        ((Temp 4) (Int)) ((Temp 5) (Int)) ((Temp 6) (Int)) ((Temp 7) (Int))
        ((Temp 8) (Int)) ((Temp 9) (Int))))
      (graph
       (((node_id 2) (next (6))
         (c
          ((inst (Pure (I (Const 1)))) (inputs) (output ((Temp 1))) (trap_stack))))
        ((node_id 6) (next (5)) (c ((inst Nop) (inputs) (output) (trap_stack))))
        ((node_id 5) (next (4))
         (c
          ((inst (Pure (I (Cmp (signed true) (comparison Cne)))))
           (inputs ((Var z_44) (Temp 1))) (output ((Temp 0))) (trap_stack))))
        ((node_id 4) (next (7 8))
         (c
          ((inst (Flow (Test_and_branch (Bool (then_value true)))))
           (inputs ((Temp 0))) (output) (trap_stack))))
        ((node_id 8) (next (18))
         (c
          ((inst (Pure (I (Const 1)))) (inputs) (output ((Var x_48)))
           (trap_stack))))
        ((node_id 7) (next (11))
         (c
          ((inst (Pure (I (Const 3)))) (inputs) (output ((Temp 3))) (trap_stack))))
        ((node_id 18) (next (21))
         (c
          ((inst (Pure (I (Const -2)))) (inputs) (output ((Temp 5)))
           (trap_stack))))
        ((node_id 11) (next (10))
         (c ((inst Nop) (inputs) (output) (trap_stack))))
        ((node_id 21) (next (20))
         (c ((inst Nop) (inputs) (output) (trap_stack))))
        ((node_id 10) (next (9))
         (c
          ((inst (Pure (I (Cmp (signed true) (comparison Cne)))))
           (inputs ((Var z_44) (Temp 3))) (output ((Temp 2))) (trap_stack))))
        ((node_id 20) (next (19))
         (c
          ((inst (Pure (I Add))) (inputs ((Var z_44) (Temp 5)))
           (output ((Var y_47))) (trap_stack))))
        ((node_id 9) (next (12 13))
         (c
          ((inst (Flow (Test_and_branch (Bool (then_value true)))))
           (inputs ((Temp 2))) (output) (trap_stack))))
        ((node_id 19) (next (3)) (c ((inst Nop) (inputs) (output) (trap_stack))))
        ((node_id 13) (next (16))
         (c
          ((inst (Pure (I (Const 245)))) (inputs) (output ((Var x_48)))
           (trap_stack))))
        ((node_id 12) (next (15))
         (c
          ((inst (Pure (Symbol camlTest__Pmakeblock_46))) (inputs)
           (output ((Temp 4))) (trap_stack))))
        ((node_id 16) (next (17))
         (c
          ((inst (Pure (I (Const 1)))) (inputs) (output ((Var y_47)))
           (trap_stack))))
        ((node_id 15) (next (14))
         (c ((inst Nop) (inputs) (output) (trap_stack))))
        ((node_id 17) (next (3)) (c ((inst Nop) (inputs) (output) (trap_stack))))
        ((node_id 14) (next (1))
         (c
          ((inst (Flow (Raise Raise_notrace))) (inputs ((Temp 4))) (output)
           (trap_stack))))
        ((node_id 3) (next (23))
         (c
          ((inst (Pure (I (Const 1024)))) (inputs) (output ((Temp 6)))
           (trap_stack))))
        ((node_id 23) (next (27))
         (c ((inst Nop) (inputs) (output) (trap_stack))))
        ((node_id 27) (next (26))
         (c
          ((inst (Pure (I Add))) (inputs ((Var x_48) (Var y_47)))
           (output ((Temp 8))) (trap_stack))))
        ((node_id 26) (next (28))
         (c
          ((inst (Pure (I (Const -1)))) (inputs) (output ((Temp 9)))
           (trap_stack))))
        ((node_id 28) (next (25))
         (c ((inst Nop) (inputs) (output) (trap_stack))))
        ((node_id 25) (next (24))
         (c
          ((inst (Pure (I Add))) (inputs ((Temp 8) (Temp 9))) (output ((Temp 7)))
           (trap_stack))))
        ((node_id 24) (next (22))
         (c ((inst Nop) (inputs) (output) (trap_stack))))
        ((node_id 22) (next (0))
         (c
          ((inst (Mem Alloc)) (inputs ((Temp 6) (Temp 7))) (output) (trap_stack)))))))
     ((current_node_id 3) (current_var_id 0) (enter_id 2) (exit_id 0)
      (raise_id 1) (temp_vars)
      (graph
       (((node_id 2) (next (0))
         (c ((inst (Pure (I (Const 1)))) (inputs) (output) (trap_stack)))))))) |}];
  List.iter graphs
    ~f:(fun g ->
      Igraph_builder.to_dot g
        ~f:(fun x ->
            let i_sexp =
              let f = Format.str_formatter in
              Format.pp_set_margin f 20;
              Sexp.pp_hum f ([%sexp_of: Dmm_intf.Dinst.t] x.inst);
              Format.flush_str_formatter ()
              |> String.substr_replace_all ~pattern:"\n" ~with_:"\\n"
            in
            let inputs =
              Array.to_list x.inputs
              |> List.map ~f:(Printf.sprintf !"i:%{sexp:Dmm_intf.Dvar.t}")
            in
            let output =
              match x.output with
              | None -> []
              | Some output ->
                [ Printf.sprintf !"o:%{sexp:Dmm_intf.Dvar.t}" output ]
            in
            String.concat
              ~sep:"\\n"
              (List.concat [ [ i_sexp ] ; inputs; output ] )
          )
      |> Compile_helper.run_graph_easy
      |> print_endline
    );
  [%expect {|
                            ┌─────────────────────┐
                            │        (Pure        │
                            │   (I (Const 1)))    │
                            │     o:(Temp 1)      │
                            └─────────────────────┘
                              │
                              │
                              ▼
                            ┌─────────────────────┐
                            │         Nop         │
                            └─────────────────────┘
                              │
                              │
                              ▼
                            ┌─────────────────────┐
                            │        (Pure        │
                            │         (I          │
                            │        (Cmp         │
                            │    (signed true)    │
                            │ (comparison Cne)))) │
                            │    i:(Var z_44)     │
                            │     i:(Temp 1)      │
                            │     o:(Temp 0)      │
                            └─────────────────────┘
                              │
                              │
                              ▼
    ┌─────────────────┐     ┌─────────────────────┐
    │                 │     │        (Flow        │
    │      (Pure      │     │  (Test_and_branch   │
    │ (I (Const 1)))  │     │        (Bool        │
    │  o:(Var x_48)   │     │     (then_value     │
    │                 │     │      true))))       │
    │                 │ ◀── │     i:(Temp 0)      │
    └─────────────────┘     └─────────────────────┘
      │                       │
      │                       │
      ▼                       ▼
    ┌─────────────────┐     ┌─────────────────────┐
    │      (Pure      │     │        (Pure        │
    │ (I (Const -2))) │     │   (I (Const 3)))    │
    │   o:(Temp 5)    │     │     o:(Temp 3)      │
    └─────────────────┘     └─────────────────────┘
      │                       │
      │                       │
      ▼                       ▼
    ┌─────────────────┐     ┌─────────────────────┐
    │       Nop       │     │         Nop         │
    └─────────────────┘     └─────────────────────┘
      │                       │
      │                       │
      ▼                       ▼
    ┌─────────────────┐     ┌─────────────────────┐
    │                 │     │        (Pure        │
    │                 │     │         (I          │
    │ (Pure (I Add))  │     │        (Cmp         │
    │  i:(Var z_44)   │     │    (signed true)    │
    │   i:(Temp 5)    │     │ (comparison Cne)))) │
    │  o:(Var y_47)   │     │    i:(Var z_44)     │
    │                 │     │     i:(Temp 3)      │
    │                 │     │     o:(Temp 2)      │
    └─────────────────┘     └─────────────────────┘
      │                       │
      │                       │
      ▼                       ▼
    ┌─────────────────┐     ┌─────────────────────┐     ┌───────────────────────────┐
    │                 │     │        (Flow        │     │                           │
    │                 │     │  (Test_and_branch   │     │           (Pure           │
    │       Nop       │     │        (Bool        │     │          (Symbol          │
    │                 │     │     (then_value     │     │ camlTest__Pmakeblock_46)) │
    │                 │     │      true))))       │     │        o:(Temp 4)         │
    │                 │     │     i:(Temp 2)      │ ──▶ │                           │
    └─────────────────┘     └─────────────────────┘     └───────────────────────────┘
      │                       │                           │
      │                       │                           │
      │                       ▼                           ▼
      │                     ┌─────────────────────┐     ┌───────────────────────────┐
      │                     │        (Pure        │     │                           │
      │                     │  (I (Const 245)))   │     │            Nop            │
      │                     │    o:(Var x_48)     │     │                           │
      │                     └─────────────────────┘     └───────────────────────────┘
      │                       │                           │
      │                       │                           │
      │                       ▼                           ▼
      │                     ┌─────────────────────┐     ┌───────────────────────────┐
      │                     │        (Pure        │     │           (Flow           │
      │                     │   (I (Const 1)))    │     │          (Raise           │
      │                     │    o:(Var y_47)     │     │      Raise_notrace))      │
      │                     │                     │     │        i:(Temp 4)         │
      │                     └─────────────────────┘     └───────────────────────────┘
      │                       │                           │
      │                       │                           │
      │                       ▼                           ▼
      │                     ┌─────────────────────┐     ┌───────────────────────────┐
      │                     │         Nop         │     │          <RAISE>          │
      │                     └─────────────────────┘     └───────────────────────────┘
      │                       │
      │                       │
      │                       ▼
      │                     ┌─────────────────────┐
      │                     │        (Pure        │
      │                     │  (I (Const 1024)))  │
      └───────────────────▶ │     o:(Temp 6)      │
                            └─────────────────────┘
                              │
                              │
                              ▼
                            ┌─────────────────────┐
                            │         Nop         │
                            └─────────────────────┘
                              │
                              │
                              ▼
                            ┌─────────────────────┐
                            │   (Pure (I Add))    │
                            │    i:(Var x_48)     │
                            │    i:(Var y_47)     │
                            │     o:(Temp 8)      │
                            └─────────────────────┘
                              │
                              │
                              ▼
                            ┌─────────────────────┐
                            │        (Pure        │
                            │   (I (Const -1)))   │
                            │     o:(Temp 9)      │
                            └─────────────────────┘
                              │
                              │
                              ▼
                            ┌─────────────────────┐
                            │         Nop         │
                            └─────────────────────┘
                              │
                              │
                              ▼
                            ┌─────────────────────┐
                            │   (Pure (I Add))    │
                            │     i:(Temp 8)      │
                            │     i:(Temp 9)      │
                            │     o:(Temp 7)      │
                            └─────────────────────┘
                              │
                              │
                              ▼
                            ┌─────────────────────┐
                            │         Nop         │
                            └─────────────────────┘
                              │
                              │
                              ▼
                            ┌─────────────────────┐
                            │     (Mem Alloc)     │
                            │     i:(Temp 6)      │
                            │     i:(Temp 7)      │
                            └─────────────────────┘
                              │
                              │
                              ▼
                            ┌─────────────────────┐
                            │       <EXIT>        │
                            └─────────────────────┘

    ┌────────────────┐
    │    <RAISE>     │
    └────────────────┘
    ┌────────────────┐
    │     (Pure      │
    │ (I (Const 1))) │
    └────────────────┘
      │
      │
      ▼
    ┌────────────────┐
    │     <EXIT>     │
    └────────────────┘ |}]
