open! Core
open! Blocks_regalloc

open! Instance

let create_dummy_graph inst =
  let out =
    Array.map inst
      ~f:(fun i ->
          { Regalloc.Instruction_node.
            i
          ; prev = [||]
          ; next = [||]
          ; id = Regalloc.Node_id.create ()
          }
        )
  in
  let length = Array.length out in
  for i = 0 to pred length do
    begin if i = 0
      then out.(i).prev <- [| Start |]
      else out.(i).prev <- [| N out.(i - 1) |]
    end;
    begin if i = pred length
      then out.(i).next <- [| End |]
      else out.(i).next <- [| N out.(i + 1) |]
    end
  done;
  out

let liveness_inst : string Instruction_with_arguments.t array =
  [| { instruction = Move
     ; inputs = [| "myin0" |]
     ; outputs = [| "tmp0" |]
     }
   ; { instruction = Move
     ; inputs = [| "tmp0" |]
     ; outputs = [| "myout0" |]
     }
  |]

let%expect_test "" =
  Regalloc.Liveness.create
    ~output:(String.Map.of_alist_exn ["myout0", Physical_register.Kind.General])
    ~input:(String.Map.of_alist_exn ["myin0", Physical_register.Kind.General])
    liveness_inst
  |> Array.iter ~f:(fun s -> print_s ([%sexp_of: Physical_register.Kind.t String.Map.t] s))
  ;
  ();
  [%expect {|
    ((myin0 General))
    ((tmp0 General))
    ((myout0 General)) |}]

let%expect_test "" =
  Regalloc.Liveness.create_from_graph
    ~output:(String.Map.of_alist_exn ["myout0", Physical_register.Kind.General])
    ~input:(String.Map.of_alist_exn ["myin0", Physical_register.Kind.General])
    (create_dummy_graph liveness_inst)
  |> [%sexp_of: String.Set.t Regalloc.Liveness.Immutable.t Regalloc.Node_id.Table.t * Physical_register.Kind.t String.Table.t]
  |> print_s
  ;
  ();
  [%expect {|
    (((0
       ((at_input (myin0)) (reads (myin0)) (defines (tmp0)) (at_output (tmp0))
        (node
         ((i ((instruction Move) (inputs (myin0)) (outputs (tmp0))))
          (prev (Start)) (next ((N 1))) (id 0)))
        (is_enter true) (is_exit false)))
      (1
       ((at_input (tmp0)) (reads (tmp0)) (defines (myout0)) (at_output (myout0))
        (node
         ((i ((instruction Move) (inputs (tmp0)) (outputs (myout0))))
          (prev ((N 0))) (next (End)) (id 1)))
        (is_enter false) (is_exit true))))
     ((myin0 General) (myout0 General) (tmp0 General))) |}]

let result_printer result =
  let regs_and_spill (regs, spill) =
    Array.append
      (Array.map regs ~f:Physical_register.to_string)
      (if spill then [| "SPILL" |] else [||])
  in
  Z3_wrap.Solver_result.Generic.map result
    ~f:(Array.map 
          ~f:(fun (instruction, register_state) ->
              Instruction_with_arguments.to_string Physical_register.to_string
                instruction
            , Register_state.map ~f:(Map.map ~f:regs_and_spill)
                register_state
            )
       )
  |> [%sexp_of: (string * (string array String.Map.t Register_state.t)) array Z3_wrap.Solver_result.Generic.t]
  |> print_s

let result_print_graph
    (result
        : Regalloc.t
         Z3i.Solver_result.t
    )
  =
  Z3_wrap.Solver_result.Generic.map result
    ~f:(fun { variable_states
            ; input_states
            ; output_states
            ; moves
            } ->
         let to_string ({ reg_set; spill } : Instance.Regalloc.Allocation_variable.Model.t) : string array =
           let regs = Set.to_array reg_set in
           Array.append
             (Array.map regs ~f:Physical_register.to_string)
             (if spill then [| "SPILL" |] else [||])
         in
         let instructions =
           Hashtbl.map variable_states
             ~f:(fun { Instance.Regalloc.Liveness.Immutable.
                       at_input
                     ; reads
                     ; defines
                     ; at_output
                     ; node
                     ; is_enter = _
                     ; is_exit = _
                     } ->
                  let to_reg v =
                    match
                      Map.find reads v
                    , Map.find defines v
                    with
                    | Some { Regalloc.Allocation_variable.Model.reg_set; _ }, _
                    | _, Some { reg_set; _} ->
                      assert (Set.length reg_set = 1);
                      let reg = Set.choose_exn reg_set in
                      Printf.sprintf !"%{Physical_register}(%s)" reg v
                    | _ -> assert false
                  in
                  let inst_string =
                    Instruction_with_arguments.to_string
                      to_reg
                      node.i
                  in
                  let register_state =
                    let before =
                      Map.map
                        at_input
                        ~f:to_string
                    in
                    let after =
                      Map.map
                        at_output
                        ~f:to_string
                    in
                    { Register_state.
                      before
                    ; after
                    }
                  in
                  inst_string
                , register_state
                )
         in
         let input = Map.map ~f:to_string input_states in
         let output = Map.map ~f:to_string output_states in
         [%sexp 
           { instructions : (string * (string array String.Map.t Register_state.t)) Regalloc.Node_id.Table.t
           ; input : string array String.Map.t
           ; output : string array String.Map.t
           ; moves : Regalloc.Move_edge.t list
           }
         ]
      )
  |> [%sexp_of: Sexp.t Z3_wrap.Solver_result.Generic.t]
  |> print_s

let run_test_graph_internal z3 ~input ~output g =
  print_endline "Graph:";
  Regalloc.allocate_graph_internal
    ~input ~output
    g
    z3
  |> result_print_graph;
  print_endline "";
  print_endline "Liveness (graph):";
  Regalloc.Liveness.create_from_graph
    ~output
    ~input
    g
  |> [%sexp_of: String.Set.t Regalloc.Liveness.Immutable.t Regalloc.Node_id.Table.t * Physical_register.Kind.t String.Table.t]
  |> print_s

let run_test_graph ~input ~output g =
  let z3 = new Z3_wrap.z3 () in
  let input = String.Map.of_alist_exn input in
  let output = String.Map.of_alist_exn output in
  run_test_graph_internal z3 ~input ~output g

let run_tests ?no_basic_block ~input ~output t =
  let z3 = new Z3_wrap.z3 () in
  let input = String.Map.of_alist_exn input in
  let output = String.Map.of_alist_exn output in
  begin match no_basic_block with
    | None ->
      print_endline "Basic Block:";
      Regalloc.allocate_basic_block_internal
        ~input ~output
        t
        z3
      |> result_printer;
      print_endline "";
    | Some () -> ()
  end;
  let g = create_dummy_graph t in
  run_test_graph_internal z3 ~input ~output g

let%expect_test "test_0" =
  run_tests
    ~output:["myout0", Physical_register.Kind.General]
    ~input:["myin0", Physical_register.Kind.General]
    [| { instruction = Move
       ; inputs = [| "myin0" |]
       ; outputs = [| "tmp0" |]
       }
     ; { instruction = Add
       ; inputs = [| "myin0"; "tmp0" |]
       ; outputs = [| "tmp1" |]
       }
     ; { instruction = Add
       ; inputs = [| "myin0"; "tmp1" |]
       ; outputs = [| "tmp2" |]
       }
     ; { instruction = Addo
       ; inputs = [| "tmp1"; "tmp2" |]
       ; outputs = [| "tmp3" |]
       }
     ; { instruction = Move
       ; inputs = [| "tmp3" |]
       ; outputs = [| "myout0" |]
       }
    |]
  ;
  [%expect {|
    Basic Block:
    (Satisfiable
     (("R1 = Move R0"
       ((before ((myin0 (R0)))) (after ((myin0 (R0)) (tmp0 (R1))))))
      ("R2 = Add R0, R1"
       ((before ((myin0 (R0)) (tmp0 (R1)))) (after ((myin0 (R0)) (tmp1 (R2))))))
      ("R1 = Add R0, R2"
       ((before ((myin0 (R0)) (tmp1 (R2)))) (after ((tmp1 (R2)) (tmp2 (R1))))))
      ("R2 = Addo R2, R1"
       ((before ((tmp1 (R2)) (tmp2 (R1)))) (after ((tmp3 (R2))))))
      ("R2 = Move R2" ((before ((tmp3 (R2)))) (after ((myout0 (R2))))))))

    Graph:
    (Satisfiable
     ((instructions
       ((2
         ("R2(tmp0) = Move R3(myin0)"
          ((before ((myin0 (R3)))) (after ((myin0 (R3)) (tmp0 (R2)))))))
        (3
         ("R2(tmp1) = Add R3(myin0), R2(tmp0)"
          ((before ((myin0 (R3)) (tmp0 (R2))))
           (after ((myin0 (R3)) (tmp1 (R2)))))))
        (4
         ("R0(tmp2) = Add R3(myin0), R2(tmp1)"
          ((before ((myin0 (R3)) (tmp1 (R2)))) (after ((tmp1 (R2)) (tmp2 (R0)))))))
        (5
         ("R2(tmp3) = Addo R2(tmp1), R0(tmp2)"
          ((before ((tmp1 (R2)) (tmp2 (R0)))) (after ((tmp3 (R2)))))))
        (6
         ("R2(myout0) = Move R2(tmp3)"
          ((before ((tmp3 (R2)))) (after ((myout0 (R2)))))))))
      (input ((myin0 (R3)))) (output ((myout0 (R2)))) (moves ())))

    Liveness (graph):
    (((2
       ((at_input (myin0)) (reads (myin0)) (defines (tmp0))
        (at_output (myin0 tmp0))
        (node
         ((i ((instruction Move) (inputs (myin0)) (outputs (tmp0))))
          (prev (Start)) (next ((N 3))) (id 2)))
        (is_enter true) (is_exit false)))
      (3
       ((at_input (myin0 tmp0)) (reads (myin0 tmp0)) (defines (tmp1))
        (at_output (myin0 tmp1))
        (node
         ((i ((instruction Add) (inputs (myin0 tmp0)) (outputs (tmp1))))
          (prev ((N 2))) (next ((N 4))) (id 3)))
        (is_enter false) (is_exit false)))
      (4
       ((at_input (myin0 tmp1)) (reads (myin0 tmp1)) (defines (tmp2))
        (at_output (tmp1 tmp2))
        (node
         ((i ((instruction Add) (inputs (myin0 tmp1)) (outputs (tmp2))))
          (prev ((N 3))) (next ((N 5))) (id 4)))
        (is_enter false) (is_exit false)))
      (5
       ((at_input (tmp1 tmp2)) (reads (tmp1 tmp2)) (defines (tmp3))
        (at_output (tmp3))
        (node
         ((i ((instruction Addo) (inputs (tmp1 tmp2)) (outputs (tmp3))))
          (prev ((N 4))) (next ((N 6))) (id 5)))
        (is_enter false) (is_exit false)))
      (6
       ((at_input (tmp3)) (reads (tmp3)) (defines (myout0)) (at_output (myout0))
        (node
         ((i ((instruction Move) (inputs (tmp3)) (outputs (myout0))))
          (prev ((N 5))) (next (End)) (id 6)))
        (is_enter false) (is_exit true))))
     ((myin0 General) (myout0 General) (tmp0 General) (tmp1 General)
      (tmp2 General) (tmp3 General))) |}]

let%expect_test "" =
  run_tests
    ~input:[ "myin0", General; "myin1", General]
    ~output:[ "myout0", General ]
  [| { instruction = Addo
     ; inputs = [| "myin0"; "myin1" |]
     ; outputs = [| "myout0" |]
     }
  |]
  ;
  [%expect {|
    Basic Block:
    (Satisfiable
     (("R2 = Addo R2, R1"
       ((before ((myin0 (R2)) (myin1 (R1)))) (after ((myout0 (R2))))))))

    Graph:
    (Satisfiable
     ((instructions
       ((7
         ("R2(myout0) = Addo R2(myin0), R1(myin1)"
          ((before ((myin0 (R2)) (myin1 (R1)))) (after ((myout0 (R2)))))))))
      (input ((myin0 (R2)) (myin1 (R1)))) (output ((myout0 (R2)))) (moves ())))

    Liveness (graph):
    (((7
       ((at_input (myin0 myin1)) (reads (myin0 myin1)) (defines (myout0))
        (at_output (myout0))
        (node
         ((i ((instruction Addo) (inputs (myin0 myin1)) (outputs (myout0))))
          (prev (Start)) (next (End)) (id 7)))
        (is_enter true) (is_exit true))))
     ((myin0 General) (myin1 General) (myout0 General))) |}]

let%expect_test "spill" =
  run_tests
    ~output:
      ["myout0", Physical_register.Kind.General]
    ~input:
      [ "myin0", Physical_register.Kind.General
      ; "myin1", Physical_register.Kind.General
      ; "myin2", Physical_register.Kind.General
      ; "myin3", Physical_register.Kind.General
      ]
    [| { instruction = Nop
       ; inputs = [| |]
       ; outputs = [|  |]
       }
     ; { instruction = Add
       ; inputs = [| "myin0"; "myin1" |]
       ; outputs = [| "tmp1" |]
       }
     ; { instruction = Add
       ; inputs = [| "myin2"; "myin3" |]
       ; outputs = [| "tmp2" |]
       }
     ; { instruction = Add
       ; inputs = [| "myin0"; "myin1" |]
       ; outputs = [| "tmp3" |]
       }
     ; { instruction = Addo
       ; inputs = [| "tmp1"; "tmp2" |]
       ; outputs = [| "tmp4" |]
       }
     ; { instruction = Addo
       ; inputs = [| "tmp4"; "tmp3" |]
       ; outputs = [| "tmp5" |]
       }
     ; { instruction = Move
       ; inputs = [| "tmp5" |]
       ; outputs = [| "myout0" |]
       }
    |]
  ;
  [%expect {|
    Basic Block:
    (Satisfiable
     ((Nop
       ((before ((myin0 (R0)) (myin1 (R2)) (myin2 (R1)) (myin3 (R3))))
        (after ((myin0 (R0)) (myin1 (R2)) (myin2 (R1)) (myin3 (R3))))))
      ("R3 = Add R0, R2"
       ((before ((myin0 (R0)) (myin1 (R2)) (myin2 (R1)) (myin3 (R3 SPILL))))
        (after
         ((myin0 (R0)) (myin1 (R2)) (myin2 (R1)) (myin3 (SPILL)) (tmp1 (R3))))))
      ("R1 = Add R1, R3"
       ((before
         ((myin0 (R0)) (myin1 (R2)) (myin2 (R1)) (myin3 (R3 SPILL))
          (tmp1 (SPILL))))
        (after ((myin0 (R0)) (myin1 (R2)) (tmp1 (SPILL)) (tmp2 (R1))))))
      ("R2 = Add R0, R2"
       ((before ((myin0 (R0)) (myin1 (R2)) (tmp1 (SPILL)) (tmp2 (R1))))
        (after ((tmp1 (SPILL)) (tmp2 (R1)) (tmp3 (R2))))))
      ("R3 = Addo R3, R1"
       ((before ((tmp1 (R3)) (tmp2 (R1)) (tmp3 (R2))))
        (after ((tmp3 (R2)) (tmp4 (R3))))))
      ("R3 = Addo R3, R2"
       ((before ((tmp3 (R2)) (tmp4 (R3)))) (after ((tmp5 (R3))))))
      ("R3 = Move R3" ((before ((tmp5 (R3)))) (after ((myout0 (R3))))))))

    Graph:
    (Satisfiable
     ((instructions
       ((8
         (Nop
          ((before ((myin0 (R2)) (myin1 (R0)) (myin2 (R1)) (myin3 (R3))))
           (after ((myin0 (R2)) (myin1 (R0)) (myin2 (R1)) (myin3 (R3)))))))
        (9
         ("R3(tmp1) = Add R2(myin0), R0(myin1)"
          ((before ((myin0 (R2)) (myin1 (R0)) (myin2 (R1)) (myin3 (R3 SPILL))))
           (after
            ((myin0 (R2)) (myin1 (R0)) (myin2 (R1)) (myin3 (SPILL)) (tmp1 (R3)))))))
        (10
         ("R1(tmp2) = Add R1(myin2), R3(myin3)"
          ((before
            ((myin0 (R2)) (myin1 (R0)) (myin2 (R1)) (myin3 (R3 SPILL))
             (tmp1 (SPILL))))
           (after ((myin0 (R2)) (myin1 (R0)) (tmp1 (SPILL)) (tmp2 (R1)))))))
        (11
         ("R0(tmp3) = Add R2(myin0), R0(myin1)"
          ((before ((myin0 (R2)) (myin1 (R0)) (tmp1 (R3)) (tmp2 (R1))))
           (after ((tmp1 (R3)) (tmp2 (R1)) (tmp3 (R0)))))))
        (12
         ("R3(tmp4) = Addo R3(tmp1), R1(tmp2)"
          ((before ((tmp1 (R3)) (tmp2 (R1)) (tmp3 (R0))))
           (after ((tmp3 (R0)) (tmp4 (R3)))))))
        (13
         ("R3(tmp5) = Addo R3(tmp4), R0(tmp3)"
          ((before ((tmp3 (R0)) (tmp4 (R3)))) (after ((tmp5 (R3)))))))
        (14
         ("R3(myout0) = Move R3(tmp5)"
          ((before ((tmp5 (R3)))) (after ((myout0 (R3)))))))))
      (input ((myin0 (R2)) (myin1 (R0)) (myin2 (R1)) (myin3 (R3))))
      (output ((myout0 (R3))))
      (moves
       (((node_in (N 9)) (node_out (N 10))
         (moves ((myin3 ((Reload R3))) (tmp1 ((Spill R3))))))
        ((node_in (N 10)) (node_out (N 11)) (moves ((tmp1 ((Reload R3))))))
        ((node_in (N 8)) (node_out (N 9)) (moves ((myin3 ((Spill R3))))))))))

    Liveness (graph):
    (((8
       ((at_input (myin0 myin1 myin2 myin3)) (reads ()) (defines ())
        (at_output (myin0 myin1 myin2 myin3))
        (node
         ((i ((instruction Nop) (inputs ()) (outputs ()))) (prev (Start))
          (next ((N 9))) (id 8)))
        (is_enter true) (is_exit false)))
      (9
       ((at_input (myin0 myin1 myin2 myin3)) (reads (myin0 myin1))
        (defines (tmp1)) (at_output (myin0 myin1 myin2 myin3 tmp1))
        (node
         ((i ((instruction Add) (inputs (myin0 myin1)) (outputs (tmp1))))
          (prev ((N 8))) (next ((N 10))) (id 9)))
        (is_enter false) (is_exit false)))
      (10
       ((at_input (myin0 myin1 myin2 myin3 tmp1)) (reads (myin2 myin3))
        (defines (tmp2)) (at_output (myin0 myin1 tmp1 tmp2))
        (node
         ((i ((instruction Add) (inputs (myin2 myin3)) (outputs (tmp2))))
          (prev ((N 9))) (next ((N 11))) (id 10)))
        (is_enter false) (is_exit false)))
      (11
       ((at_input (myin0 myin1 tmp1 tmp2)) (reads (myin0 myin1)) (defines (tmp3))
        (at_output (tmp1 tmp2 tmp3))
        (node
         ((i ((instruction Add) (inputs (myin0 myin1)) (outputs (tmp3))))
          (prev ((N 10))) (next ((N 12))) (id 11)))
        (is_enter false) (is_exit false)))
      (12
       ((at_input (tmp1 tmp2 tmp3)) (reads (tmp1 tmp2)) (defines (tmp4))
        (at_output (tmp3 tmp4))
        (node
         ((i ((instruction Addo) (inputs (tmp1 tmp2)) (outputs (tmp4))))
          (prev ((N 11))) (next ((N 13))) (id 12)))
        (is_enter false) (is_exit false)))
      (13
       ((at_input (tmp3 tmp4)) (reads (tmp3 tmp4)) (defines (tmp5))
        (at_output (tmp5))
        (node
         ((i ((instruction Addo) (inputs (tmp4 tmp3)) (outputs (tmp5))))
          (prev ((N 12))) (next ((N 14))) (id 13)))
        (is_enter false) (is_exit false)))
      (14
       ((at_input (tmp5)) (reads (tmp5)) (defines (myout0)) (at_output (myout0))
        (node
         ((i ((instruction Move) (inputs (tmp5)) (outputs (myout0))))
          (prev ((N 13))) (next (End)) (id 14)))
        (is_enter false) (is_exit true))))
     ((myin0 General) (myin1 General) (myin2 General) (myin3 General)
      (myout0 General) (tmp1 General) (tmp2 General) (tmp3 General)
      (tmp4 General) (tmp5 General))) |}]

let%expect_test "loop" =
  let instructions =
    let rec add0 =
      { Regalloc.Instruction_node.
        i =
          { instruction = Add
          ; inputs = [| "myin0"; "myin1" |]
          ; outputs = [| "tmp1" |]
          }
      ; prev = [| Start |]
      ; next = [| N loop |]
      ; id = Regalloc.Node_id.create ()
      }
    and loop =
      { Regalloc.Instruction_node.
        i =
          { instruction = Loop
          ; inputs = [| "myin1" |]
          ; outputs = [| "myin1" |]
          }
      ; prev = [| N add0 |]
      ; next = [| N add0 ; N add1 |]
      ; id = Regalloc.Node_id.create ()
      }
    and add1 =
      { Regalloc.Instruction_node.
        i =
          { instruction = Add
          ; inputs = [| "tmp1"; "myin0" |]
          ; outputs = [| "myout0" |]
          }
      ; prev = [| N loop |]
      ; next = [| End |]
      ; id = Regalloc.Node_id.create ()
      }
    in
    [| add0
     ; loop
     ; add1
    |]
  in
  run_test_graph
    ~output:
      [ "myout0", Physical_register.Kind.General
      ]
    ~input:
      [ "myin0", Physical_register.Kind.General
      ; "myin1", Physical_register.Kind.General
      ]
    instructions
  ;
  [%expect {|
    Graph:
    (Satisfiable
     ((instructions
       ((15
         ("R2(tmp1) = Add R3(myin0), R0(myin1)"
          ((before ((myin0 (R3)) (myin1 (R0))))
           (after ((myin0 (R3)) (myin1 (R0)) (tmp1 (R2)))))))
        (16
         ("R0(myin1) = Loop R0(myin1)"
          ((before ((myin0 (R3)) (myin1 (R0)) (tmp1 (R2))))
           (after ((myin0 (R3)) (myin1 (R0)) (tmp1 (R2)))))))
        (17
         ("R3(myout0) = Add R2(tmp1), R3(myin0)"
          ((before ((myin0 (R3)) (tmp1 (R2)))) (after ((myout0 (R3)))))))))
      (input ((myin0 (R3)) (myin1 (R0)))) (output ((myout0 (R3)))) (moves ())))

    Liveness (graph):
    (((15
       ((at_input (myin0 myin1)) (reads (myin0 myin1)) (defines (tmp1))
        (at_output (myin0 myin1 tmp1))
        (node
         ((i ((instruction Add) (inputs (myin0 myin1)) (outputs (tmp1))))
          (prev (Start)) (next ((N 16))) (id 15)))
        (is_enter true) (is_exit false)))
      (16
       ((at_input (myin0 myin1 tmp1)) (reads (myin1)) (defines (myin1))
        (at_output (myin0 myin1 tmp1))
        (node
         ((i ((instruction Loop) (inputs (myin1)) (outputs (myin1))))
          (prev ((N 15))) (next ((N 15) (N 17))) (id 16)))
        (is_enter false) (is_exit false)))
      (17
       ((at_input (myin0 tmp1)) (reads (myin0 tmp1)) (defines (myout0))
        (at_output (myout0))
        (node
         ((i ((instruction Add) (inputs (tmp1 myin0)) (outputs (myout0))))
          (prev ((N 16))) (next (End)) (id 17)))
        (is_enter false) (is_exit true))))
     ((myin0 General) (myin1 General) (myout0 General) (tmp1 General)))
     |}]
