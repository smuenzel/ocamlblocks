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
  |> clean_sexp
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
  List.filter_map filtered_cmm
    ~f:(function 
        | Cdata _ -> None
        | Cfunction f ->
          Tcmm.type_function
            ~fun_args:f.fun_args
            f.fun_body
          |> Some
      )
  |> [%sexp_of: Tcmm.Texpr.t list]
  |> clean_sexp
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
     ((Cconst_int 1) (Int))) |}]
