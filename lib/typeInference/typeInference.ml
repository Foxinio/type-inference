(** Type inference (for simple types) *)

open Core.Imast
open Core

open Unify

(* ========================================================================= *)
(* Type inference *)

let node_with_type ({ data; start_pos; end_pos;_} : ('a, 'b) Ast.node) (typ : Type.t) : ('a, Type.t) Ast.node =
  { data; typ; start_pos; end_pos }

let unwrap node env var opt =
  match opt with
  | Some t -> t
  | None ->
    let name = Env.lookup_var_name env var |>
      Option.value ~default:"<unknown>" in
    Utils.report_error node "Undefined variable: %s" name

(** Typing environments *)
let rec infer env (node : Imast.expl_type Imast.expr) : Type.t Imast.expr =
  let data, typ = infer_type env node in
  unify typ (convert_type node env node.typ);
  { node with data; typ }
and convert_type node env explicit_type : Type.t =
  let unwrap = unwrap node env in
  match explicit_type with
  | Imast.TUnit -> Type.t_unit
  | Imast.THole -> Type.fresh_uvar ()
  | Imast.TBool -> Type.t_bool
  | Imast.TInt  -> Type.t_int
  | Imast.TArrow(tps, tp) ->
    let tps = List.map (convert_type node env) tps in
    let tp = convert_type node env tp in
    Type.t_arrow tps tp
  | Imast.TProd tps ->
    let tps = List.map (convert_type node env) tps in
    Type.t_prod tps
  | Imast.TVar v -> Env.lookup_delta env v |> unwrap v
  | Imast.TSchema (name, tps) ->
    let tps = List.map (convert_type node env) tps in
    Utils.report_error node "This language feature is not supported yet!"

and infer_type env (e : Imast.expl_type Imast.expr) : Type.t Imast.expr_data * Type.t =
  let unwrap name = unwrap e env name in
  let extend_list xs env =
    let extend (tps, env) x =
      let new_tp = Type.fresh_gvar () in
      unify new_tp (snd x);
      new_tp :: tps, Env.extend_gamma env x (Type.typ_mono new_tp)
    in
    List.fold_left extend ([], env) xs
  and convert_var env ((name,typ) : expl_type var) =
    name, convert_type e env typ
  in
  match e.data with
  | EUnit   -> EUnit,   Type.t_unit
  | EBool b -> EBool b, Type.t_bool
  | ENum  n -> ENum  n, Type.t_int
  | EVar  (name,typ) ->
    let typ' = convert_type e env typ in
    let instantiated = Env.lookup_gamma env name
      |> unwrap name
      |> Type.instantiate in
    EVar (name, typ'), instantiated
  | EFn(xs, body) ->
    let xs : Type.t var list = List.map (convert_var env) xs in
    let tps, env = extend_list xs env in
    let body' = infer env body in
    EFn (xs, body'), Type.t_arrow tps body'.typ
  | EFix(f, xs, body) ->
    let xs = List.map (convert_var env) xs in
    let tps, env = extend_list xs env in
    let tp2 = Type.fresh_uvar () in
    let f = convert_var env f in
    let f_tp = Type.t_arrow tps tp2 in
    let env = Env.extend_gamma env f (Type.typ_mono f_tp) in
    let body' = check_type env body tp2 in
    EFix(f, xs, body'), f_tp
  | EApp(e1, es) ->
    let generate _ = Type.fresh_uvar () in
    let tps = List.map generate es in
    let tp1 = Type.fresh_uvar () in
    let e1' = check_type env e1 (Type.t_arrow tps tp1) in
    let es' = List.map2 (fun e tp -> check_type env e tp) es tps in
    EApp(e1', es'), tp1
  | ELet(x, e1, e2) ->
    let e1' = infer env e1 in
    let x = convert_var env x in
    let tp = Type.generalize (Env.get_uvars env) e1'.typ in
    let e2' = infer (Env.extend_gamma env x tp) e2 in
    ELet(x, e1', e2'), e2'.typ
  | EPair(e1, e2) ->
    let e1' = infer env e1 in
    let e2' = infer env e2 in
    EPair(e1', e2'), Type.t_pair e1'.typ e2'.typ
  | EFst e ->
    let tp1 = Type.fresh_uvar () in
    let tp2 = Type.fresh_uvar () in
    let e' = check_type env e (Type.t_pair tp1 tp2) in
    EFst e', tp1
  | ESnd e ->
    let tp1 = Type.fresh_uvar () in
    let tp2 = Type.fresh_uvar () in
    let e' = check_type env e (Type.t_pair tp1 tp2) in
    ESnd e', tp2
  | EIf(e1, e2, e3) ->
    let e1' = check_type env e1 Type.t_bool in
    let e2' = infer env e2 in
    let e3' = check_type env e3 e2'.typ in
    EIf(e1', e2', e3'), e2'.typ
  | ESeq(e1, e2) ->
    let e1' = check_type env e1 Type.t_unit in
    let e2' = infer env e2 in
    ESeq(e1', e2'), e2'.typ
  | EAbsurd e ->
    let e' = check_type env e Type.t_empty in
    EAbsurd e', Type.fresh_uvar ()

    (* TODO: Finish from here *)
  | EType ((scheme_name,scheme_args), ctor_defs, rest) ->
    Utils.report_error e "This language feature is not supported yet!"
  | ETypeAlias ((scheme_name,scheme_args), typ, rest) ->
    Utils.report_error e "This language feature is not supported yet!"
  | ECtor (name, body) ->
    Utils.report_error e "This language feature is not supported yet!"
  | EMatch (e, clauses) ->
    Utils.report_error e "This language feature is not supported yet!"

and check_type env e tp =
  let open PrettyPrinter in
  let e' = infer env e in
  try
    unify tp e'.typ;
    e'
  with
  | Cannot_unify ->
    let ctx = pp_context () in
    Utils.report_error e
      "This expression has type %s, but an expression was expected of type %s."
      (pp_type ctx 0 e'.typ)
      (pp_type ctx 0 tp)


