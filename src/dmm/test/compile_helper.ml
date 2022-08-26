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

let extra_header = 
{|

external ( = ) : 'a -> 'a -> bool = "%equal"
external ( <> ) : 'a -> 'a -> bool = "%notequal"
external ( < ) : 'a -> 'a -> bool = "%lessthan"
external ( > ) : 'a -> 'a -> bool = "%greaterthan"
external ( <= ) : 'a -> 'a -> bool = "%lessequal"
external ( >= ) : 'a -> 'a -> bool = "%greaterequal"
external compare : 'a -> 'a -> int = "%compare"

external ( == ) : 'a -> 'a -> bool = "%eq"
external ( != ) : 'a -> 'a -> bool = "%noteq"

external not : bool -> bool = "%boolnot"
external ( && ) : bool -> bool -> bool = "%sequand"
external ( || ) : bool -> bool -> bool = "%sequor"

external ( ~- ) : int -> int = "%negint"
external ( ~+ ) : int -> int = "%identity"
external succ : int -> int = "%succint"
external pred : int -> int = "%predint"
external ( + ) : int -> int -> int = "%addint"
external ( - ) : int -> int -> int = "%subint"
external ( * ) : int -> int -> int = "%mulint"
external ( / ) : int -> int -> int = "%divint"
external ( mod ) : int -> int -> int = "%modint"

external ( land ) : int -> int -> int = "%andint"
external ( lor ) : int -> int -> int = "%orint"
external ( lxor ) : int -> int -> int = "%xorint"

external ( lsl ) : int -> int -> int = "%lslint"
external ( lsr ) : int -> int -> int = "%lsrint"
external ( asr ) : int -> int -> int = "%asrint"
|} 

let compile_structure str =
  let str = extra_header ^ str in
  Clflags.native_code := true;
  Clflags.no_std_include := true;
  Clflags.nopervasives := true;
  Clflags.afl_instrument := false;
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
            ~initially_opened_module:None (* (Some "Stdlib") *)
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

let run_graph_easy g =
  let exe = "/usr/bin/graph-easy" in
  let process_info =
    Core_unix.create_process
      ~prog:exe
      ~args:[ "--as=boxart" ]
  in
  let to_proc = Core_unix.out_channel_of_descr process_info.stdin in
  Out_channel.output_string to_proc g;
  Out_channel.close to_proc;
  let of_proc = Core_unix.in_channel_of_descr process_info.stdout in
  In_channel.input_all of_proc

let%expect_test "graph-easy" =
  let g =
    {|
digraph graphname
 {
     a [ label = "x\ny"];
     a -> b -> c;
     b -> d;
 }
      |}
  in
  run_graph_easy g
  |> print_endline;
  [%expect {|
              ┌───┐
              │ x │
              │ y │
              └───┘
                │
                │
                ▼
    ┌───┐     ┌───┐
    │ d │ ◀── │ b │
    └───┘     └───┘
                │
                │
                ▼
              ┌───┐
              │ c │
              └───┘ |}]


  
