open! Core
    

module Phase = struct
  type t = Int.Set.t [@@deriving sexp_of]

  let t_of_sexp = function
    | Sexp.Atom _ as sexp ->
      [%of_sexp: int] sexp
      |> Int.Set.singleton
    | List [ List (Atom _ :: _) as sexp ]
    | (List ([] | Atom _ :: _) as sexp) ->
      [%of_sexp: int list] sexp
      |> Int.Set.of_list
    | other ->
      raise_s [%message "not a phase spec"
          (other : Sexp.t)
      ]
end

module Phaseconf = struct
  type t =
    { phase : Phase.t
    } [@@deriving sexp]
end

let is_phase = function
  | Sexp.List
      [ Atom "phase"
      ; phase
      ] ->
    Phase.t_of_sexp phase
    |> Some
  | Sexp.List
      (Atom "phase"
         :: phases)
      ->
    Phase.t_of_sexp (Sexp.List phases)
    |> Some
  | _ -> None

let rec to_phase apply_phase (sexp : Sexp.t) =
  match sexp with
  | Sexp.Atom _ -> Some sexp
  | Sexp.List list ->
    let phases, rest =
      List.partition_map
        list
        ~f:(function
            | Sexp.List
                (Atom "phase"
                 :: phase
                ) ->
              First (Phase.t_of_sexp (Sexp.List phase))
            | sexp -> Second sexp
          )
    in
    match phases with
    | [] ->
      to_phase_list apply_phase rest
    | [ one_phase ] ->
      if Set.mem one_phase apply_phase
      then to_phase_list apply_phase rest
      else None
    | more_than_one_phase ->
      raise_s [%message "multipled phase stanzas at same level"
          (more_than_one_phase : Int.Set.t list)
      ]
and to_phase_list apply_phase sexps =
  List.filter_map sexps ~f:(to_phase apply_phase)
  |> Sexp.List
  |> Some

let%expect_test "" =
  let input =
    Sexp.of_string_many
      {|
      (foo bar)
      (phase 0)
      (hello world)
      (record
         (phase (1))
         (important x)
      )
    |}
    |> Sexp.List
  in
  let () =
    to_phase 0 input
    |> function
    | None -> ()
    | Some sexp -> print_s sexp
  in
  [%expect {| ((foo bar) (hello world)) |}];
  let () =
    to_phase 1 input
    |> function
    | None -> ()
    | Some sexp -> print_s sexp
  in
  [%expect {| |}];
  let input =
    Sexp.of_string_many
      {|
      (foo bar)
      (hello world)
      (record
         (phase 1)
         (important x)
      )
    |}
    |> Sexp.List
  in
  let () =
    to_phase 0 input
    |> function
    | None -> ()
    | Some sexp -> print_s sexp
  in
  [%expect {| ((foo bar) (hello world)) |}];
  let () =
    to_phase 1 input
    |> function
    | None -> ()
    | Some sexp -> print_s sexp
  in
  [%expect {| ((foo bar) (hello world) (record (important x))) |}];
  ()
