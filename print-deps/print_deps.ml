open! Core

type t =
  { for_impl : string list
  ; for_intf : string list
  } [@@deriving sexp]

type input = string * t [@@deriving sexp]

let () =
  print_endline "digraph {\n";
  In_channel.iter_lines In_channel.stdin
    ~f:(fun s ->
        let mname, deps =
          Sexp.of_string s
          |> Sexp.of_sexp_allow_extra_fields_recursively [%of_sexp: input]
        in
        printf "%s\n" mname;
        List.iter deps.for_impl
          ~f:(fun impl ->
              printf "%s -> %s [color=black]\n" mname impl
            );
        List.iter deps.for_intf
          ~f:(fun intf ->
              printf "%s -> %s [color=red]\n" mname intf
            );
      );
  print_endline "}\n"

