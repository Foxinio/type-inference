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

let get_type (node : Type.typ Imast.expr) = Type.get_template node.typ

(** Typing environments *)
let rec infer env (node : Imast.expl_type Imast.expr) : Type.typ Imast.expr =
  let data, typ = infer_type env node in
  (* TODO: make sure subtyping is correct direction *)
  unify_subtype (convert_type node env node.typ) typ;
  { node with data; typ=Type.typ_mono typ }

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
  | Imast.TVar name -> 
    let tp = Env.lookup_delta env name |> unwrap name in
    if Type.TVarSet.is_empty (Type.get_arguments tp) then Env.instantiate env tp
    else Utils.report_error node "Alias used without parameters: %s" (var_name env name)
  | Imast.TAlias (name, tps) ->
    let typ = Env.lookup_delta env name |> unwrap name in
    let set = Type.get_arguments typ in
    if Type.TVarSet.is_empty set then
      Utils.report_error node "Alias used without parameters: %s" (var_name env name)
    else
      let mapping = List.map (convert_type node env) tps |>
          List.to_seq |>
          Seq.zip (Type.TVarSet.to_seq set) |>
          Type.TVarMap.of_seq in
      Env.instantiate env ~mapping typ

and infer_type env (e : Imast.expl_type Imast.expr) : Type.typ Imast.expr_data * Type.t =
  let unwrap name = unwrap e env name in
  let gen_mapping uvar_set =
    let uvar_seq = Type.TVarSet.to_seq uvar_set |>
      Seq.map (fun uvar -> (uvar, Env.fresh_uvar env)) in
    let mapping = Type.TVarMap.of_seq uvar_seq in
    let instance_args = Seq.unzip uvar_seq |> snd |> List.of_seq in
    mapping, instance_args
  in
  let convert_var env ((name,typ) : expl_type var) =
    name, convert_type e env typ
  in
  let extend_list xs env =
    let extend (tps1, tps2, env) x =
      let name, expl = convert_var env x in
      let new_tp = Env.fresh_gvar env in
      unify_equal new_tp expl;
      let new_typ = Type.typ_mono new_tp in
      (name, new_typ) :: tps1, new_tp :: tps2, Env.extend_gamma env (name,new_typ)
    in
    List.fold_left extend ([], [], env) xs
  in
  match e.data with
  | EUnit   -> EUnit,   Type.t_unit
  | EBool b -> EBool b, Type.t_bool
  | ENum  n -> ENum  n, Type.t_int

  | EVar  (name,typ) ->
    let typ' = convert_type e env typ in
    let schema = Env.lookup_gamma env name
      |> unwrap name in
    let instantiated = Env.instantiate env schema in
    unify_equal typ' instantiated;
    EVar (name, schema), instantiated

  | EFn(xs, body) ->
    let xs, tps, env = extend_list xs env in
    let body' = infer env body in
    EFn (xs, body'), split_tarrow tps (get_type body')

  | EFix(f, xs, body) ->
    let xs, tps, env = extend_list xs env in
    let tp2 = Env.fresh_uvar env in
    let (f, expl) = convert_var env f in
    let f_tp = split_tarrow tps tp2 in
    unify_equal f_tp expl;
    let f = f, Type.typ_mono f_tp in
    let env = Env.extend_gamma env f in
    let body' = infer_and_check_type env body tp2 in
    EFix(f, xs, body'), f_tp

  | EApp(e1, es) ->
    let generate _ = Env.fresh_uvar env in
    let tps = List.map generate es in
    let tp1 = Env.fresh_uvar env in
    let e1' = infer_and_check_type env e1 (Type.t_arrow tps tp1) in
    let es' = List.map2 (fun e tp -> infer_and_check_type env e tp) es tps in
    EApp(e1', es'), tp1

  | ELet(x, e1, e2) ->
    let env' = Env.increase_level_let env in
    let (x, tp) = convert_var env' x in
    let e1' = infer_and_check_type env' e1 tp in
    let e1_typ = get_type e1' in
    let x = x, Env.generalize env' e1_typ in
    let e2' = infer (Env.extend_gamma env x) e2 in
    ELet(x, e1', e2'), get_type e2'

  | EPair(e1, e2) ->
    let e1' = infer env e1 in
    let tp1 = get_type e1' in
    let e2' = infer env e2 in
    let tp2 = get_type e2' in
    EPair(e1', e2'), Type.t_pair tp1 tp2

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
    let res_tp = get_type e2' in
    let e3' = infer_and_check_type env e3 res_tp in
    EIf(e1', e2', e3'), res_tp

  | ESeq(e1, e2) ->
    let e1' = infer_and_check_type env e1 Type.t_unit in
    let e2' = infer env e2 in
    ESeq(e1', e2'), get_type e2'

  | EType ((name,arg_list) as alias, ctor_defs, rest) ->
    let out_type = Env.fresh_uvar env in
    let env = Env.increase_level_type env in
    let arg_list = List.map (fun x -> (x, Type.TVar.fresh ())) arg_list in
    let set = List.map snd arg_list |> Type.TVarSet.of_list in
    let arg_list = List.map (fun (x,t) -> x, Type.t_var t) arg_list in
    let tvars = List.map snd arg_list in
    let env = Env.extend_delta_with_adt env name tvars set in
    let env' = Env.extend_delta_of_list env arg_list in
    let f (name, typ) = name, convert_type e env' typ |> Type.typ_schema set in
    let ctor_defs' = List.map f ctor_defs in
    let env = Env.extend_by_ctors env ctor_defs' name tvars set  in
    let rest' = infer_and_check_type env rest out_type in
    EType(alias, ctor_defs', rest'), get_type rest'

  | ECtor (name, body) ->
    let expected_typ, alias_typ = Env.lookup_ctor env name |> unwrap name in
    let var_set = Type.get_arguments alias_typ in
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
    let typ' = convert_type e env' typ |> Type.typ_schema set in
    let env = Env.extend_delta_with_alias env (name, typ') in
    let rest' = infer env rest in
    ETypeAlias(alias, typ', rest'), get_type rest'

  | EMatch (sub_expr, ((ctor_name, _, _) :: _ as clauses)) ->
    let _, adt_typ = Env.lookup_ctor env ctor_name |> unwrap ctor_name in
    let var_set = Type.get_arguments adt_typ in
    let mapping, instance_args = gen_mapping var_set in
    let adt_t = Env.instantiate ~mapping env adt_typ in
    let sub_expr' = infer_and_check_type env sub_expr adt_t in
    let out_type = Env.fresh_uvar env in
    let f (ctor_name, (var_name, var_type), e) =
      let typ, _ = Env.lookup_ctor env ctor_name |> unwrap ctor_name in
      let expected_type = Env.instantiate ~mapping env typ in
      unify_subtype expected_type (convert_type e env var_type);
      let env = Env.extend_gamma env (var_name, Type.typ_mono expected_type) in
      ctor_name, (var_name, Type.typ_mono expected_type), infer_and_check_type env e out_type
    in
    let clauses' = List.map f clauses in
    EMatch (sub_expr', clauses'), out_type

  | EMatch (sub_expr, []) ->
    let sub_expr' = infer_and_check_type env sub_expr Type.t_empty in
    EMatch (sub_expr', []), Env.fresh_uvar env

and infer_and_check_type env e tp =
  let open PrettyPrinter in
  let e' = infer env e in
  try
    unify_subtype tp @@ get_type e';
    e'
  with
  | Cannot_unify ->
    let ctx = Env.seq_of_var_name env |> pp_context_of_seq in
    Utils.report_error e
      "This expression has type %s, but an expression was expected of type %s."
      (pp_type ctx @@ get_type e')
      (pp_type ctx tp)

type program = Type.typ Imast.expr * string Imast.VarTbl.t

let infer ((p, env) : Imast.program) : program =
  let inner_env = Env.of_var_names env in
  let data, typ = infer_type inner_env p in
  (* should be a better way to return generalized type *)
  let typ = Type.generalize Type.Level.starting typ in
  { p with data; typ }, env
