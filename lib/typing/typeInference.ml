(** Type inference (for simple types) *)

open Core.Imast
module Imast = Core.Imast
module Utils = Core.Utils

(* ========================================================================= *)
(* Type inference *)

let unwrap node env var opt =
  match opt with
  | Some t -> t
  | None ->
    let name = Env.lookup_var_name env var in
    Utils.report_error node "Undefined variable: %s" name


let make_mono tp eff =
  Schema.typ_mono tp, eff

let get_tp ({typ=typ,_;_} : (Schema.typ*Effect.t) expr) =
  Schema.get_template typ
let get_eff ({typ=_,eff;_} : (Schema.typ*Effect.t) expr) = eff

(** inference function *)
let rec infer env (node : Imast.expl_type Imast.expr) =
  let data, typ, eff = infer_type env node in
  Unify.subtype ~supertype:(convert_type node env node.typ) ~subtype:typ;
  { node with data; typ=(Schema.typ_mono typ, eff) }

and convert_type node env explicit_type : Type.t =
  let unwrap = unwrap node env in
  match explicit_type with
  | Imast.TUnit -> Type.t_unit
  | Imast.THole -> Env.fresh_uvar env
  | Imast.TBool -> Type.t_bool
  | Imast.TInt  -> Type.t_int
  | Imast.TArrow(eff, tp1, tp2) ->
    let tp1 = convert_type node env tp1 in
    let tp2 = convert_type node env tp2 in
    let uv  = Env.wrap_eff_uvar env eff in
    Type.t_arrow uv tp1 tp2
  | Imast.TPair (tp1, tp2) ->
    let tp1 = convert_type node env tp1 in
    let tp2 = convert_type node env tp2 in
    Type.t_pair tp1 tp2
  | Imast.TVar name -> 
    let tp = Env.lookup_delta env name |> unwrap name in
    if Type.TVarSet.is_empty (Schema.get_arguments tp)
    then Env.instantiate env tp
    else
      Utils.report_error node
        "Alias used without parameters: %s"
        (Env.lookup_var_name env name)
  | Imast.TAlias (name, tps) ->
    let typ = Env.lookup_delta env name |> unwrap name in
    let set = Schema.get_arguments typ in
    if Type.TVarSet.is_empty set then
      Utils.report_error node
        "Alias used without parameters: %s"
        (Env.lookup_var_name env name)
    else
      let mapping = List.map (convert_type node env) tps
        |> List.to_seq
        |> Seq.zip (Type.TVarSet.to_seq set)
        |> Type.TVarMap.of_seq
      in
      Env.instantiate env ~mapping typ

and infer_type env (e : Imast.expl_type Imast.expr) =
  let unwrap name = unwrap e env name in
  let gen_mapping uvar_set =
    let uvar_seq = Type.TVarSet.to_seq uvar_set |>
      Seq.map (fun uvar -> (uvar, Env.fresh_uvar env)) in
    let mapping = Type.TVarMap.of_seq uvar_seq in
    let instance_args = Seq.unzip uvar_seq
      |> snd
      |> List.of_seq
    in mapping, instance_args
  in
  let convert_var env ((name,typ) : expl_type var) =
      let expl = convert_type e env typ in
      let new_typ = Schema.typ_mono expl in
      (name, (new_typ, Effect.EffPure)), expl
  in
  match e.data with
  | EUnit   -> EUnit,   Type.t_unit, Effect.EffPure
  | EBool b -> EBool b, Type.t_bool, Effect.EffPure
  | ENum  n -> ENum  n, Type.t_int, Effect.EffPure

  | EExtern (name, typ, _) ->
    let expl = convert_type e env typ in
    let arg = Env.fresh_uvar env in
    let res = Env.fresh_uvar env in
    let uve = Env.fresh_eff_uvar env in
    let tp = Type.t_arrow uve arg res in
    Unify.equal expl tp;
    EExtern (name, make_mono expl (Effect.view uve),
      make_mono arg Effect.EffUnknown),
    expl,
    Effect.view uve

  | EVar  (name,typ) ->
    let expl = convert_type e env typ in
    let schema = Env.lookup_gamma env name
      |> unwrap name in
    let instantiated = Env.instantiate env schema in
    Unify.subtype ~supertype:expl ~subtype:instantiated;
    EVar (name, (schema, EffPure)), instantiated, Effect.EffPure

  | EFn(x, body) ->
    let var, typ = convert_var env x in
    let env = Env.extend_gamma env var in
    let body' = infer env body in
    let uve = Env.wrap_eff_uvar env @@ get_eff body' in
    EFn (var, body'),
    Type.t_arrow uve typ (get_tp body'),
    EffPure

  | EFix(f, x, body) ->
    let var, typ = convert_var env x in
    let env = Env.extend_gamma env var in
    (* since its EFix this has to be impure *)
    let f, tres = convert_var env f in
    let uve = Env.wrap_eff_uvar env Effect.EffImpure in
    let f_tp = Type.t_arrow uve typ tres in
    let env = Env.extend_gamma env f in
    let body' = infer_and_check_type env body tres in
    EFix(f, var, body'), f_tp, Effect.EffPure

  | EApp(e1, e2) ->
    let tp2 = Env.fresh_uvar env in
    let tp1 = Env.fresh_uvar env in
    let uve = Env.fresh_eff_uvar env in
    let e1_tp = Type.t_arrow uve tp2 tp1 in
    let e1' = infer_and_check_type env e1 e1_tp in
    let e2' = infer_and_check_type env e2 tp2 in
    EApp(e1', e2'), tp1, Effect.view uve

  | ELet((x,tp), e1, e2) ->
    let env' = Env.increase_level_major env in
    let tp = convert_type e env' tp in
    let e1' = infer_and_check_type env' e1 tp in
    (* TODO: Add value restriction *)
    let x = x, (Env.generalize env' (get_tp e1'), Effect.EffPure) in
    let e2' = infer (Env.extend_gamma env x) e2 in
    ELet(x, e1', e2'), get_tp e2', get_eff e2'

  | EPair(e1, e2) ->
    let e1' = infer env e1 in
    let e2' = infer env e2 in
    let eff = Effect.join (get_eff e1') (get_eff e2') in
    EPair(e1', e2'), Type.t_pair (get_tp e1') (get_tp e2'), eff

  | EFst e ->
    let tp1 = Env.fresh_uvar env in
    let tp2 = Env.fresh_uvar env in
    let e' = infer_and_check_type env e (Type.t_pair tp1 tp2) in
    EFst e', tp1, get_eff e'
  | ESnd e ->
    let tp1 = Env.fresh_uvar env in
    let tp2 = Env.fresh_uvar env in
    let e' = infer_and_check_type env e (Type.t_pair tp1 tp2) in
    ESnd e', tp2, get_eff e'

  | EIf(e1, e2, e3) ->
    let e1' = infer_and_check_type env e1 Type.t_bool in
    let e2' = infer env e2 in
    let res_tp = get_tp e2' in
    let e3' = infer_and_check_type env e3 res_tp in
    let eff = Effect.join (get_eff e1') (get_eff e2') in
    let eff = Effect.join eff (get_eff e3') in
    EIf(e1', e2', e3'), res_tp, eff

  | ESeq(e1, e2) ->
    let e1' = infer_and_check_type env e1 Type.t_unit in
    let e2' = infer env e2 in
    let eff = Effect.join (get_eff e1') (get_eff e2') in
    ESeq(e1', e2'), get_tp e2', eff

  | EType ((name,arg_list) as alias, ctor_defs, rest) ->
    let out_type = Env.fresh_uvar env in
    let env = Env.increase_level_minor env in
    let arg_list = List.map (fun x -> (x, Type.TVar.fresh ())) arg_list in
    let set = List.map snd arg_list |> Type.TVarSet.of_list in
    let arg_list = List.map (fun (x,t) -> x, Type.t_var t) arg_list in
    let tvars = List.map snd arg_list in
    let env = Env.extend_delta_with_adt env name tvars set in
    let env' = Env.extend_delta_of_list env arg_list in
    let f (name, typ) =
      let typ = convert_type e env' typ  in
      name, (Schema.typ_schema set typ, Effect.EffPure) in
    let ctor_defs' = List.map f ctor_defs in
    let env = Env.extend_by_ctors env ctor_defs' name tvars set  in
    let rest' = infer_and_check_type env rest out_type in
    EType(alias, ctor_defs', rest'), get_tp rest', get_eff rest'

  | ECtor (name, body) ->
    let expected_typ, alias_typ = Env.lookup_ctor env name |> unwrap name in
    let var_set = Schema.get_arguments alias_typ in
    let mapping, alias_args = gen_mapping var_set in
    let expected_type = Env.instantiate ~mapping env expected_typ in
    let alias_t = Env.instantiate ~mapping env alias_typ in
    let body' = infer_and_check_type env body expected_type in
    ECtor (name, body'), alias_t, Effect.EffPure

  | ETypeAlias ((name, arg_list) as alias, typ, rest) ->
    let arg_list = List.map (fun x -> (x, Type.TVar.fresh ())) arg_list in
    let set = List.map snd arg_list |> Type.TVarSet.of_list in
    let arg_list = List.map (fun (x,t) -> x, Type.t_var t) arg_list in
    let env' = Env.extend_delta_of_list env arg_list in
    let typ' = convert_type e env' typ |> Schema.typ_schema set in
    let env = Env.extend_delta_with_alias env (name, typ') in
    let typ' = typ', Effect.EffPure in
    let rest' = infer env rest in
    ETypeAlias(alias, typ', rest'), get_tp rest', get_eff rest'

  | EMatch (sub_expr, ((ctor_name, _, _) :: _ as clauses)) ->
    (* since we allow recursive types this may result in a loop,
        making this impure *)

    let _, adt_typ = Env.lookup_ctor env ctor_name |> unwrap ctor_name in
    let var_set = Schema.get_arguments adt_typ in
    let mapping, instance_args = gen_mapping var_set in
    let adt_t = Env.instantiate ~mapping env adt_typ in
    let sub_expr' = infer_and_check_type env sub_expr adt_t in
    let out_type = Env.fresh_uvar env in
    let f (ctor_name, (var_name, var_type), e) =
      let typ, _ = Env.lookup_ctor env ctor_name |> unwrap ctor_name in
      let expected_type = Env.instantiate ~mapping env typ in
      Unify.subtype
        ~supertype:expected_type
        ~subtype:(convert_type e env var_type);
      let typ = Schema.typ_mono expected_type, Effect.EffPure in
      let env = Env.extend_gamma env (var_name, typ) in
      ctor_name, (var_name, typ), infer_and_check_type env e out_type
    in
    let clauses' = List.map f clauses in
    EMatch (sub_expr', clauses'), out_type, Effect.EffImpure

  | EMatch (sub_expr, []) ->
    let sub_expr' = infer_and_check_type env sub_expr Type.t_empty in
    EMatch (sub_expr', []), Env.fresh_uvar env, get_eff sub_expr'

and infer_and_check_type env e expected =
  let open PrettyPrinter in
  let e' = infer env e in
  try
    Unify.subtype
      ~supertype:expected
      ~subtype:(get_tp e');
    e'
  with
  | Unify.Cannot_unify ->
    let ctx = Env.seq_of_var_name env |> pp_context_of_seq in
    Utils.report_error e
      "This expression has type %s, but an expression was expected of type %s."
      (pp_type ctx @@ get_tp e')
      (pp_type ctx expected)
  | Type.Levels_difference (adt, adtlvl, uvarlvl) ->
    Utils.report_error e
      "Levels difference [%s>>%s]: %s escapes scope."
      (Type.Level.to_string adtlvl)
      (Type.Level.to_string uvarlvl)
      (Env.lookup_var_name env adt)

type program = (Schema.typ * Effect.t) Imast.expr * string Imast.VarTbl.t

let infer ((p, env) : Imast.program) : program =
  let inner_env = Env.of_var_names env in
  let data, typ, eff = infer_type inner_env p in
  (* should be a better way to return generalized type *)
  let typ = Schema.generalize Type.Level.starting typ in
  { p with data; typ=typ,eff }, env
