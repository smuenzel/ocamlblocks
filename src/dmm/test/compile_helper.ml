open! Core
open! Ocamlc_kit

type t =
  { parsetree : Parsetree.structure
  ; typedtree : Typedtree.structure
  ; lambda : Lambda.program
  ; simplif_lambda : Lambda.lambda
  ; clambda_convert : Clambda.with_constants
  ; cmm : Cmm.phrase list
  } [@@deriving sexp_of]

module Platform = (val Asmcomp_platform.(platform default_platform))
module Arch = Platform.Arch
module Proc = Platform.Proc

let empty_formatter : Format.formatter =
  Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())

module Backend = struct
  (* See backend_intf.mli. *)

  let symbol_for_global' = Compilenv.symbol_for_global'
  let closure_symbol = Compilenv.closure_symbol

  let really_import_approx = Import_approx.really_import_approx
  let import_symbol = Import_approx.import_symbol

  let size_int = Arch.size_int
  let big_endian = Arch.big_endian

  let max_sensible_number_of_arguments =
    (* The "-1" is to allow for a potential closure environment parameter. *)
    Proc.max_arguments_for_tailcalls - 1
end
let backend = (module Backend : Backend_intf.S)

let compile_structure str =
  Clflags.native_code := true;
  let parsetree = Parse.implementation (Lexing.from_string str) in
  (* {[
       Load_path.init
         (ld_library_path_contents ())
       ;
     ]} *)
  Cmt_format.clear ();
  Typecore.reset_delayed_checks ();
  Env.reset_required_globals ();
  Compilenv.reset "Test";
  let typedtree = 
    let ttstr, _, _, _, _ =
      try
        let env =
          Typemod.initial_env
            ~loc:Location.none
            ~initially_opened_module:(Some "Stdlib")
            ~open_implicit_modules:[]
        in
        Typemod.type_structure env parsetree
      with
      | Typetexp.Error (_,_,error) ->
        raise_s [%message "error typing" (error : Typetexp.error)]
    in
    ttstr
  in
  let lambda =
    Translmod.transl_implementation_flambda "Test" (typedtree,Tcoerce_none)
  in
  let simplif_lambda =
    Simplif.simplify_lambda lambda.code
  in
  let clambda_convert =
    Flambda_middle_end.lambda_to_clambda
      ~ppf_dump:empty_formatter
      ~prefixname:""
      ~backend
      { lambda with code = simplif_lambda
      }
  in
  let cmm : Cmm.phrase list =
    Cmmgen.compunit
      (module Platform)
      clambda_convert
  in
  { parsetree : Parsetree.structure
  ; typedtree : Typedtree.structure
  ; lambda : Lambda.program
  ; simplif_lambda : Lambda.lambda
  ; clambda_convert : Clambda.with_constants
  ; cmm : Cmm.phrase list
  }
