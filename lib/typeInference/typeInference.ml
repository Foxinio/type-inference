(** Type inference (for simple types) *)

open Core.Imast
open Core

open Unify

(* ========================================================================= *)
(* Type inference *)

let var_name env var =
    Env.lookup_var_name env var |>
      Option.value ~default:"<unknown>"

let unwrap node env var opt =
  match opt with
  | Some t -> t
  | None ->
    let name = var_name env var in
    Utils.report_error node "Undefined variable: %s" name

let split_tarrow =
  let f arg res = Type.t_arrow [arg] res in
  List.fold_right f

(** Typing environments *)
let rec infer env (node : Imast.expl_type Imast.expr) : Type.t Imast.expr =
  let data, typ = infer_type env node in
  unify typ (convert_type node env node.typ);
  { node with data; typ }
and convert_type node env explicit_type : Type.t =
  let unwrap = unwrap node env in
  match explicit_type with
  | Imast.TUnit -> Type.t_unit
  | Imast.THole -> Env.fresh_uvar env
  | Imast.TBool -> Type.t_bool
  | Imast.TInt  -> Type.t_int
  | Imast.TArrow(tps, tp) ->
    let tps = List.map (convert_type node env) tps in
    let tp = convert_type node env tp in
    Type.t_arrow tps tp
  | Imast.TProd tps ->
    let tps = List.map (convert_type node env) tps in
    Type.t_prod tps
  | Imast.TVar v -> 
    let (typ, set) = Env.lookup_delta env v |> unwrap v in
    if Type.TVarSet.is_empty set then Env.instantiate env typ
    else 
      Utils.report_error node "Alias used without parameters: %s" (var_name env v)
  | Imast.TAlias (name, tps) ->
    let (typ, set) = Env.lookup_delta env name |> unwrap name in
    let mapping = List.map (convert_type node env) tps |>
          List.to_seq |>
          Seq.zip (Type.TVarSet.to_seq set) |>
          Type.TVarMap.of_seq in
    Env.instantiate env ~mapping typ

and infer_type env (e : Imast.expl_type Imast.expr) : Type.t Imast.expr_data * Type.t =
  let unwrap name = unwrap e env name in
  let gen_mapping uvar_set =
    let uvar_seq = Type.TVarSet.to_seq uvar_set |>
      Seq.map (fun uvar -> (uvar, Env.fresh_uvar env)) in
    let mapping = Type.TVarMap.of_seq uvar_seq in
    let instance_args = Seq.unzip uvar_seq |> snd |> List.of_seq in
    mapping, instance_args
  in
  let extend_list xs env =
    let extend (tps, env) x =
      let new_tp = Env.fresh_gvar env in
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
      |> unwrap name in
    EVar (name, typ'), instantiated
  | EFn(xs, body) ->
    let xs : Type.t var list = List.map (convert_var env) xs in
    let tps, env = extend_list xs env in
    let body' = infer env body in
    EFn (xs, body'), split_tarrow tps body'.typ
  | EFix(f, xs, body) ->
    let xs = List.map (convert_var env) xs in
    let tps, env = extend_list xs env in
    let tp2 = Env.fresh_uvar env in
    let f = convert_var env f in
    let f_tp = split_tarrow tps tp2 in
    let env = Env.extend_gamma env f (Type.typ_mono f_tp) in
    let body' = infer_and_check_type env body tp2 in
    EFix(f, xs, body'), f_tp
  | EApp(e1, es) ->
    (* this doesn't work, at some point any gvar will be unified with uvar
      and at that point any information about multiarg function
      that might be kept in uvar will be lost *)
    let generate _ = Env.fresh_uvar env in
    let tps = List.map generate es in
    let tp1 = Env.fresh_uvar env in
    let e1' = infer_and_check_type env e1 (Type.t_arrow tps tp1) in
    let es' = List.map2 (fun e tp -> infer_and_check_type env e tp) es tps in
    EApp(e1', es'), tp1
  | ELet(x, e1, e2) ->
    let env' = Env.increase_level env in
    let e1' = infer env' e1 in
    let x = convert_var env' x in
    let tp = Env.generalize env' e1'.typ in
    let e2' = infer (Env.extend_gamma env x tp) e2 in
    ELet(x, e1', e2'), e2'.typ
  | EPair(e1, e2) ->
    let e1' = infer env e1 in
    let e2' = infer env e2 in
    EPair(e1', e2'), Type.t_pair e1'.typ e2'.typ
  | EFst e ->
    let tp1 = Env.fresh_uvar env in
    let tp2 = Env.fresh_uvar env in
    let e' = infer_and_check_type env e (Type.t_pair tp1 tp2) in
    EFst e', tp1
  | ESnd e ->
    let tp1 = Env.fresh_uvar env in
    let tp2 = Env.fresh_uvar env in
    let e' = infer_and_check_type env e (Type.t_pair tp1 tp2) in
    ESnd e', tp2
  | EIf(e1, e2, e3) ->
    let e1' = infer_and_check_type env e1 Type.t_bool in
    let e2' = infer env e2 in
    let e3' = infer_and_check_type env e3 e2'.typ in
    EIf(e1', e2', e3'), e2'.typ
  | ESeq(e1, e2) ->
    let e1' = infer_and_check_type env e1 Type.t_unit in
    let e2' = infer env e2 in
    ESeq(e1', e2'), e2'.typ
  | EAbsurd e ->
    let e' = infer_and_check_type env e Type.t_empty in
    EAbsurd e', Env.fresh_uvar env

  | EType ((name,arg_list) as alias, ctor_defs, rest) ->
    let out_type = Env.fresh_uvar env in
    let env = Env.increase_level env in
    let arg_list = List.map (fun x -> (x, Type.TVar.fresh ())) arg_list in
    let set = List.map snd arg_list |> Type.TVarSet.of_list in
    let arg_list = List.map (fun (x,t) -> x, Type.t_var t) arg_list in
    let tvars = List.map snd arg_list in
    let env = Env.extend_delta_with_adt env name tvars set in
    let env' = Env.extend_delta_of_list env arg_list in
    let ctor_defs = List.map (convert_var env') ctor_defs in
    let f (name, typ) = name, Type.typ_schema set typ in
    let ctor_defs' = List.map f ctor_defs in
    let env = Env.extend_by_ctors env ctor_defs' name tvars set  in
    let rest' = infer_and_check_type env rest out_type in
    EType(alias, ctor_defs, rest'), rest'.typ

  | ECtor (name, body) ->
    let expected_typ, var_set, alias_typ = Env.lookup_ctor env name |> unwrap name in
    let mapping, alias_args = gen_mapping var_set in
    let expected_type = Env.instantiate ~mapping env expected_typ in
    let alias_t = Env.instantiate ~mapping env alias_typ in
    let body' = infer_and_check_type env body expected_type in
    ECtor (name, body'), alias_t

  | ETypeAlias ((name, arg_list) as alias, typ, rest) ->
    let arg_list = List.map (fun x -> (x, Type.TVar.fresh ())) arg_list in
    let set = List.map snd arg_list |> Type.TVarSet.of_list in
    let arg_list = List.map (fun (x,t) -> x, Type.t_var t) arg_list in
    let env' = Env.extend_delta_of_list env arg_list in
    let typ = convert_type e env' typ in
    let typ' = Type.typ_schema set typ in
    let env = Env.extend_delta_with_alias env (name, typ') set in
    let rest' = infer env rest in
    ETypeAlias(alias, typ, rest'), rest'.typ

  | EMatch (sub_expr, ((ctor_name, _, _) :: _ as clauses)) ->
    let _, var_set, adt_typ = Env.lookup_ctor env ctor_name |> unwrap ctor_name in
    let mapping, instance_args = gen_mapping var_set in
    let adt_t = Env.instantiate ~mapping env adt_typ in
    let sub_expr' = infer_and_check_type env sub_expr adt_t in
    let out_type = Env.fresh_uvar env in
    let f (ctor_name, (var_name, var_type), e) =
      let typ, _, _ = Env.lookup_ctor env ctor_name |> unwrap ctor_name in
      let expected_type = Env.instantiate ~mapping env typ in
      unify expected_type (convert_type e env var_type);
      let env = Env.extend_gamma env (var_name, expected_type)
        (Type.typ_mono expected_type) in
      ctor_name, (var_name, expected_type), infer_and_check_type env e out_type
    in
    let clauses' = List.map f clauses in
    EMatch (sub_expr', clauses'), out_type
  | EMatch _ ->
    Utils.report_error e "cannot have match with no clauses"

and infer_and_check_type env e tp =
  let open PrettyPrinter in
  let e' = infer env e in
  try
    unify tp e'.typ;
    e'
  with
  | Cannot_unify ->
    let ctx = Env.seq_of_var_name env |> pp_context_of_seq in
    Utils.report_error e
      "This expression has type %s, but an expression was expected of type %s."
      (pp_type ctx 0 e'.typ)
      (pp_type ctx 0 tp)

type program = Type.t Imast.expr * string Imast.VarTbl.t

let infer ((p, env) : Imast.program) : program =
  let inner_env = Env.of_var_names env in
  let data, typ = infer_type inner_env p in
  (* should be a better way to return generalized type *)
  let _tp = Type.generalize Type.Level.starting typ in
  { p with data; typ }, env
