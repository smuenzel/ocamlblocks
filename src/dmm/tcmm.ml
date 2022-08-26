open! Core

module Cmm = Ocamlc_kit.Cmm

module Dvar = Dmm_intf.Dvar

module Gen_expr = struct
  open Cmm

  type 'expr t =
      Cconst_int of int * Debuginfo.t
    | Cconst_natint of nativeint * Debuginfo.t
    | Cconst_float of float * Debuginfo.t
    | Cconst_symbol of string * Debuginfo.t
    | Cvar of Dvar.t
    | Clet of Dvar.t * 'expr * 'expr
    | Clet_mut of Dvar.t * machtype
                  * 'expr * 'expr
    | Cassign of Dvar.t * 'expr
    | Ctuple of 'expr list
    | Cop of operation * 'expr list * Debuginfo.t
    | Csequence of 'expr * 'expr
    | Cifthenelse of 'expr * Debuginfo.t * 'expr
                     * Debuginfo.t * 'expr * Debuginfo.t
    | Cswitch of 'expr * int array * ('expr * Debuginfo.t) array
                 * Debuginfo.t
    | Ccatch of
        rec_flag
        * (int * (Dvar.t * machtype) list
           * 'expr * Debuginfo.t) list
        * 'expr
    | Cexit of int * 'expr list
    | Ctrywith of 'expr * Dvar.t * 'expr
                  * Debuginfo.t
  [@@deriving sexp_of]

  let t4_m3 ~f (a,b,c,d) = (a,b,f c,d)

  let rec map : 'a 'b. f:(map:('a t -> 'b t) -> 'a -> 'b) -> 'a t -> 'b t =
    fun (type a b) ~(f : map :(a t -> b t) -> a -> b) t ->
    let f e = f ~map:(map ~f) e in
    match t with
    | Cconst_int (c,d) -> Cconst_int (c,d)
    | Cconst_natint (c,d) -> Cconst_natint (c,d)
    | Cconst_float (c,d) -> Cconst_float (c,d)
    | Cconst_symbol (s,d) -> Cconst_symbol (s,d)
    | Cvar v -> Cvar v
    | Clet (v,e1,e2) -> Clet (v, f e1, f e2)
    | Clet_mut (v,m,e1,e2) -> Clet_mut (v,m,f e1,f e2)
    | Cassign (v,e) -> Cassign (v,f e)
    | Ctuple list -> Ctuple (List.map ~f list)
    | Cop (o, list, d) -> Cop (o, List.map ~f list, d)
    | Csequence (e1, e2) -> Csequence (f e1, f e2)
    | Cifthenelse (e1, d1, e2, d2, e3, d3) ->
      Cifthenelse (f e1, d1, f e2, d2, f e3, d3)
    | Cswitch (e1, ar, array, d) ->
      Cswitch (f e1, ar, Array.map ~f:(Tuple2.map_fst ~f) array, d)
    | Ccatch (r,list,e) ->
      Ccatch (r, List.map ~f:(t4_m3 ~f) list, f e)
    | Cexit (i, list) -> Cexit (i, List.map ~f list)
    | Ctrywith (e1, v, e2, d) -> Ctrywith (f e1, v, f e2, d)

end

let machtype_equal (a : Cmm.machtype) (b : Cmm.machtype) =
  Array.equal Poly.equal a b

let join_machtype_exn (a : Cmm.machtype) (b : Cmm.machtype) =
  if machtype_equal a b
  then a
  else Array.map2_exn a b ~f:Cmm.lub_component

module Tcell : sig
  type t [@@deriving sexp_of]

  val create : Cmm.machtype option -> t
  val create_empty : unit -> t

  val t : t -> Cmm.machtype option
  val t_exn : t -> Cmm.machtype
  
  val addr : unit -> t
  val int : unit -> t
  val float : unit -> t
  val val_t : unit -> t
  val void : unit -> t

  val unify_exn : t -> t -> unit
  val unify_ret_exn : t -> t -> t

  val unify_t_exn : t -> Cmm.machtype -> unit

  val copy : t -> t
end = struct
  type t = Cmm.machtype option UnionFind.elem

  let sexp_of_t t =
    UnionFind.get t
    |> [%sexp_of: Cmm.machtype option]

  let create m = UnionFind.make m
  let create_some m = create (Some m)
  let create_empty () = create None

  let t t = UnionFind.get t
  let t_exn t' = Option.value_exn (t t')

  let addr () = create_some Cmm.typ_addr
  let int () = create_some Cmm.typ_int
  let float () = create_some Cmm.typ_float
  let val_t () = create_some Cmm.typ_val
  let void () = create_some Cmm.typ_void

  let unify_ret_exn a b =
    UnionFind.merge
      (fun a b ->
         match a, b with
         | None, None -> None
         | Some _ as x, None
         | None, (Some _ as x) -> x
         | Some a, Some b ->
           Some (join_machtype_exn a b)
      )
      a b

  let unify_exn a b =
    unify_ret_exn a b
    |> (ignore : t -> unit)

  let unify_t_exn t typ =
    let res =
      match UnionFind.get t with
      | None -> Some typ
      | Some typ' ->
        Some (join_machtype_exn typ' typ)
    in
    UnionFind.set t res

  let copy t =
    create (UnionFind.get t)
end

module Texpr_cell = struct
  type t = T : t Gen_expr.t * Tcell.t -> t [@@deriving sexp_of]
end

module Texpr = struct
  type t = T : t Gen_expr.t * Cmm.machtype -> t

  let rec sexp_of_t (T (ge, mt)) =
    [%sexp_of: t Gen_expr.t * Cmm.machtype] (ge, mt)
end

module Env : sig
  type t

  val create : unit -> t

  val var : t -> Dvar.t -> Tcell.t
  val exit : t -> int -> Tcell.t

  val all_vars : t -> (Dvar.t * Tcell.t) list

end = struct
  type t =
    { vars : Tcell.t Dvar.Table.t
    ; exits : Tcell.t Int.Table.t
    }

  let create () = 
    { vars = Dvar.Table.create ()
    ; exits = Int.Table.create ()
    }

  let var t dvar =
    Hashtbl.find_or_add t.vars dvar ~default:Tcell.create_empty

  let all_vars t =
    Hashtbl.to_alist t.vars

  let exit t i =
    Hashtbl.find_or_add t.exits i ~default:Tcell.create_empty
end

module Renv : sig
  type t

  val of_env : Env.t -> t

  val var_exn : t -> Dvar.t -> Cmm.machtype
  val make_var_exn : t -> Dvar.t -> Cmm.machtype -> unit
end = struct

  type t =
    { vars : Cmm.machtype Dvar.Table.t
    }

  let of_env env =
    let vars =
      Env.all_vars env
      |> List.map
        ~f:(Tuple2.map_snd
              ~f:(fun tcell ->
                  Option.value ~default:Cmm.typ_void (Tcell.t tcell)
                )
           )
      |> Dvar.Table.of_alist_exn
    in
    { vars }

  let var_exn t var = Hashtbl.find_exn t.vars var
  let make_var_exn t var typ = Hashtbl.add_exn t.vars ~key:var ~data:typ
end

let array_map_reduce_exn ~f_map ~f_red ar =
  let length = Array.length ar in
  assert (length >= 0);
  let acc = ref (f_map ar.(0)) in
  for i = 1 to pred length do
    acc := f_red !acc (f_map ar.(i))
  done;
  !acc

let rec type_all ~env cmm : Texpr_cell.t =
  match cmm with
  | Cmm.Cconst_int (c,d) -> T (Cconst_int (c,d), Tcell.int ())
  | Cconst_natint (c,d) -> T (Cconst_natint (c,d), Tcell.int ())
  | Cconst_float (c,d) -> T (Cconst_float (c, d), Tcell.float ())
  | Cconst_symbol (s,d) -> T (Cconst_symbol (s,d), Tcell.int ())
  | Cvar v ->
    let v = Dvar.Var v in
    T (Cvar v, Env.var env v)
  | Clet (v, d_expr, in_expr) ->
    let v = Dvar.Var (Backend_var.With_provenance.var v) in
    let (T (_, d_typ) as d_expr) = type_all ~env d_expr in
    Tcell.unify_exn d_typ (Env.var env v);
    let (T (_, typ) as in_expr) = type_all ~env in_expr in
    T (Clet (v, d_expr, in_expr), typ)
  | Clet_mut (v, v_typ, d_expr, in_expr) ->
    let v = Dvar.Var (Backend_var.With_provenance.var v) in
    let (T (_, d_typ) as d_expr) = type_all ~env d_expr in
    let var_typ = Env.var env v in
    Tcell.unify_t_exn var_typ v_typ;
    Tcell.unify_exn var_typ d_typ;
    let (T (_, typ) as in_expr) = type_all ~env in_expr in
    T (Clet_mut (v, v_typ, d_expr, in_expr), typ)
  | Cphantom_let (_, _, expr) ->
    type_all ~env expr
  | Cassign (v , d_expr) ->
    let v = Dvar.Var v in
    let (T (_, d_typ) as d_expr) = type_all ~env d_expr in
    Tcell.unify_exn d_typ (Env.var env v);
    T (Cassign (v, d_expr), Tcell.void ())
  | Ctuple exprs ->
    let exprs = List.map exprs ~f:(type_all ~env) in
    let typ =
      (* CR smuenzel: not lazy, so possibly not correct *)
      List.map ~f:(fun (Texpr_cell.T (_, typ)) -> Tcell.t_exn typ) exprs
      |> Array.concat
    in
    T (Ctuple exprs, Tcell.create (Some typ))
  | Cop (op, exprs, dbg) ->
    let exprs = List.map exprs ~f:(type_all ~env) in
    let typ = 
      let open Cmm in
      (* Copied from selectgen *)
      match op with
        Capply ty -> Tcell.create (Some ty)
      | Cextcall(_s, ty_res, _ty_args, _alloc) -> Tcell.create (Some ty_res)
      | Cload {memory_chunk; _ } ->
        begin match memory_chunk with
          | Word_val -> Tcell.val_t ()
          | Single | Double -> Tcell.float ()
          | Byte_unsigned | Byte_signed | Sixteen_unsigned | Sixteen_signed
          | Thirtytwo_unsigned | Thirtytwo_signed | Word_int -> Tcell.int ()
        end
      | Calloc -> Tcell.val_t ()
      | Cstore (_c, _) -> Tcell.void ()
      | Cdls_get -> Tcell.val_t ()
      | Caddi | Csubi | Cmuli | Cmulhi | Cdivi | Cmodi |
        Cand | Cor | Cxor | Clsl | Clsr | Casr |
        Ccmpi _ | Ccmpa _ | Ccmpf _ -> Tcell.int ()
      | Caddv -> Tcell.val_t ()
      | Cadda -> Tcell.addr ()
      | Cnegf | Cabsf | Caddf | Csubf | Cmulf | Cdivf -> Tcell.float ()
      | Cfloatofint -> Tcell.float ()
      | Cintoffloat -> Tcell.int ()
      | Craise _ -> Tcell.create_empty ()
      | Ccheckbound -> Tcell.void ()
      | Copaque -> Tcell.val_t ()
    in
    T (Cop (op, exprs, dbg), typ)
  | Csequence (expr0, expr1) ->
    let expr0 = type_all ~env expr0 in
    let (T (_, typ) as expr1) = type_all ~env expr1 in
    T (Csequence (expr0, expr1), typ)
  | Cifthenelse (discriminant, dbg_if, ifso, dbg_ifso, ifnot, dbg_ifnot) ->
    let discriminant = type_all ~env discriminant in
    let (T (_, t_ifso) as ifso) = type_all ~env ifso in
    let (T (_, t_ifnot) as ifnot) = type_all ~env ifnot in
    Tcell.unify_exn t_ifso t_ifnot;
    T (Cifthenelse (discriminant, dbg_if, ifso, dbg_ifso, ifnot, dbg_ifnot), t_ifso)
  | Cswitch (discriminant, idx, cases, dbg) ->
    let discriminant = type_all ~env discriminant in
    let cases =
      Array.map cases
        ~f:(Tuple2.map_fst ~f:(type_all ~env))
    in
    let typ =
      array_map_reduce_exn
        ~f_map:(fun ((Texpr_cell.T (_, typ)), _) -> typ)
        ~f_red:Tcell.unify_ret_exn
        cases
    in
    T (Cswitch (discriminant, idx, cases, dbg), typ)
  | Ccatch (rec_flag,list,expr) ->
    let (T (_, t_expr) as expr) = type_all ~env expr in
    let list =
      List.map list
        ~f:(fun (num, vars, exit_expr, dbg) ->
            let vars =
              List.map vars
                ~f:(fun (bv, typ) ->
                    let v = Dvar.Var (Backend_var.With_provenance.var bv) in
                    let tcell = Env.var env v in
                    Tcell.unify_t_exn tcell typ;
                    v, typ
                  )
            in
            let (T (_,exit_type) as exit_expr) = type_all ~env exit_expr in
            Tcell.unify_exn (Env.exit env num) exit_type;
            Tcell.unify_exn t_expr exit_type;
            (num, vars, exit_expr, dbg)
          )
    in
    T (Ccatch (rec_flag, list, expr), t_expr)
  | Cexit (num, exprs) ->
    (* CR smuenzel: doesn't get propagated to types from enclosing catch *)
    let exprs = List.map exprs ~f:(type_all ~env) in
    T (Cexit (num, exprs), Tcell.create_empty ())
  | Ctrywith (body, exn, handler, dbg) ->
    let (T (_, t_body) as body) = type_all ~env body in 
    let (T (_, t_handler) as handler) = type_all ~env handler in
    Tcell.unify_exn t_body t_handler;
    let exn = Dvar.Var (Backend_var.With_provenance.var exn) in
    T (Ctrywith (body, exn, handler, dbg), t_body)

let type_function ~fun_args cmm =
  let env = Env.create () in
  List.iter fun_args
    ~f:(fun (v,t) ->
        Tcell.unify_t_exn
          (Env.var env (Var (Backend_var.With_provenance.var v)))
          t
      );
  let f ~map (Texpr_cell.T (e, tcell)) =
    let typ =
      match Tcell.t tcell with
      | Some typ -> typ
      | None -> Cmm.typ_void
    in
    Texpr.T (map e, typ)
  in
  let app_f = f ~map:(Gen_expr.map ~f) in
  type_all ~env cmm
  |> app_f



