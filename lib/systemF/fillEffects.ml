open Core
open Main
open Subst

let refresh_tvars = EnsureWellTyped.check_well_scoped

(* ========================================================================= *)
(* Analysis *)

let rec unify_subtypes tp1 tp2 =
  match tp1, tp2 with
  | TUnit, TUnit
  | TEmpty, TEmpty
  | TBool, TBool
  | TInt, TInt -> ()
  | TVar x, TVar y when TVar.compare x y = 0 -> ()
  | TArrow(arr1, ta1, tb1), TArrow(arr2, ta2, tb2) ->
    Arrow.unify_uvar arr1 arr2;
    unify_subtypes ta2 ta1;
    unify_subtypes tb1 tb2

  | TForallT(a1, tp1), TForallT(a2, tp2) ->
    let lst = Seq.forever (fun () -> TVar(TVar.fresh ()))
      |> Seq.take (List.length a1)
      |> List.of_seq in
    begin try
        unify_subtypes (subst_list tp1 a1 lst) (subst_list tp2 a2 lst)
      with Invalid_argument _ ->
        Utils.report_internal_error "SystemF: unbound tvar"
    end

  | TPair (tp1a, tp1b), TPair (tp2a, tp2b) ->
    unify_subtypes tp1a tp2a;
    unify_subtypes tp1b tp2b

  | (TUnit | TEmpty | TBool | TInt | TVar _  | TADT (_, _)
    | TArrow (_, _, _) | TPair(_, _) | TForallT (_, _)), _ ->
    Utils.report_internal_error "cannot unity in systemF"

let unify_eqtype tp1 tp2 =
  unify_subtypes tp1 tp2;
  unify_subtypes tp2 tp1

let extend_var env xs tp =
  let rec inner env xs tp arr =
    match xs, tp with
    | x :: xs, TArrow(arr, tp1, tp2) ->
      inner (Env.add_var env x tp1) xs tp2 arr
    | [], tp -> tp, env, arr
    | _ :: _, _ -> failwith "internal error: expected TArrow"
  in
  match xs, tp with
  | x :: xs, TArrow(arr, tp1, tp2) ->
    inner (Env.add_var env x tp1) xs tp2 arr
  | _ -> failwith "internal error: expected TArrow"

let rec fill_effects env e =
  let open Effect in
  match e with
  | EUnit   -> TUnit, EffPure
  | EBool _ -> TBool, EffPure
  | ENum _  -> TInt, EffPure
  | EVar x  -> Env.lookup_var env x, EffPure

  | EFn (args, body, tp) ->
    let tp' = refresh_tvars env tp in
    let tres, env, arr = extend_var env args tp' in
    let eff = check_type env body tres in
    if eff = EffImpure then Arrow.set_impure arr;
    tp', EffPure

  | EFix (f, args, body, tp) ->
    let tp' = refresh_tvars env tp in
    let env = Env.add_var env f tp' in
    let tres, env, arr = extend_var env args tp' in
    Arrow.set_impure arr;
    let _ = check_type env body tres in
    tp', EffPure

  | EApp (e1, es) ->
    let tp1, eff = fill_effects env e1 in
    let tres, eff = fill_effects_in_app env es tp1 eff in
    tres, eff

  | ETFn(a, body) ->
    let env, b = Env.extend_tvar env a in
    let tp, eff = fill_effects env body in
    TForallT(b, tp), eff

  | ETApp(e, tps) ->
    begin match fill_effects env e with
    | TForallT(args, body), eff when List.length args = List.length tps ->
      let tps = List.map (refresh_tvars env) tps in
      subst_list body args tps, eff
    | _ -> failwith "Internal type error"
    end

  | ELet(x, e1, e2) ->
    let tp1, eff1 = fill_effects env e1 in
    let env = Env.add_var env x tp1 in
    let tp2, eff2 = fill_effects env e2 in
    tp2, Effect.join eff1 eff2

  | EExtern(_, tp) ->
    refresh_tvars env tp, EffPure

  | EPair(e1, e2) ->
    let tp1, eff1 = fill_effects env e1 in
    let tp2, eff2 = fill_effects env e2 in
    TPair(tp1, tp2), Effect.join eff1 eff2

  | EFst e ->
    begin match fill_effects env e with
    | TPair (tp1, _), eff -> tp1, eff
    | _ -> failwith "Internal type error"
    end

  | ESnd e ->
    begin match fill_effects env e with
    | TPair(_, tp2), eff -> tp2, eff
    | _ -> failwith "Internal type error"
    end

  | EIf(e1, e2, e3) ->
    let eff1 = check_type env e1 TBool in
    let tp2, eff2 = fill_effects env e2 in
    let tp3, eff3 = fill_effects env e3 in
    unify_eqtype tp2 tp3;
    tp2, Effect.join eff1 (Effect.join eff2 eff3)

  | ESeq(e1, e2) ->
    let eff1 = check_type env e1 TUnit in
    let tp, eff2 = fill_effects env e2 in
    tp, Effect.join eff1 eff2

  | EType(alias, tvars, ctor_defs, body) ->
    let env', tvars = Env.extend_tvar env tvars in
    let env = Env.extend_ctors env' ctor_defs alias tvars in
    fill_effects env body

  | ECtor (name, body) ->
    let expected, alias, tvars = Env.lookup_ctor env name in
    let tp, eff = fill_effects env body in
    let adt_args = Subst.get_subst (Env.tvar_set env) expected tp |> List.map snd in
    TADT (alias, adt_args), eff

  | EMatch(body, defs, tp) ->
    let tp' = refresh_tvars env tp in
    begin match fill_effects env body with
    | TADT(alias, args), _ ->
      let f (ctor, x, e) =
        let expected, alias', tvars = Env.lookup_ctor env ctor in
        assert (Imast.IMAstVar.compare alias alias' = 0);
        let substituted = Subst.subst_list expected tvars args in
        let env = Env.add_var env x substituted in
        let _ = check_type env e tp' in
        ()
      in
      List.iter f defs;
      tp', EffImpure
    | TEmpty, eff1 ->
      assert(List.length defs = 0);
      tp', eff1
    | _ -> failwith "internal type error"
    end

and check_type env e tp =
  let tp', eff' = fill_effects env e in
  unify_subtypes tp' tp;
  eff'

and fill_effects_in_app env args tp eff1 =
  let rec inner args tp eff =
    match args, tp with
    | [], tres -> tres, eff
    | e :: args, TArrow(arr, targ, tres) ->
      let targ', eff' = fill_effects env e in
      unify_subtypes targ' targ;
      let eff' = Effect.join eff' @@ Arrow.view_eff arr in
      inner args tres (Effect.join eff eff')
    | _ :: _, _ -> Utils.report_internal_error "Application with too many arguments"
  in
  match args, tp with
  | e :: args, TArrow(arr, targ, tres) ->
    let targ', eff' = fill_effects env e in
    unify_subtypes targ' targ;
    let eff' = Effect.join eff' @@ Arrow.view_eff arr in
    inner args tres eff'
  |  _ -> Utils.report_internal_error "Application with too many arguments"

(* ========================================================================= *)
(* Transformation *)

(** Returns expression being applied to,
      and list of expressions being applied,
      such that deepest arguments (those first to be applied)
      are at the begining of the list*)
let extract_apps e =
  let rec inner acc e =
    match e with
    | EApp (e1, es) -> inner (es @ acc) e1
    | _ -> e, acc
  in inner [] e

let rec transform_expr env e : expr * tp * Effect.t =
  match e with
  | EUnit -> e, TUnit, EffPure
  | EBool _ -> e, TBool, EffPure
  | ENum _ -> e, TInt, EffPure
  | EVar x -> EVar x, Env.lookup_var env x, EffPure

  | EFn (xs, body, tp) ->
    let tp' = refresh_tvars env tp in
    let _, env, _ = Env.extend_var env xs tp' in
    let body', _, eff  = transform_expr env body in
    EFn (xs, body', tp'), tp', EffPure

  | EFix (f, xs, body, tp) ->
    let tp' = refresh_tvars env tp in
    let _, env, _ = Env.extend_var env xs tp' in
    let body', _, eff = transform_expr (Env.add_var env f tp') body in
    EFix (f, xs, body', tp'), tp', EffPure

  | EApp (_, _) ->
    let e1, es = extract_apps e in
    let e1' = transform_expr env e1 in
    let f e =
      let e', _, eff = transform_expr env e in
      e', eff
    in
    let es' = List.map f es in
    transform_app env e1' es'

  | EExtern (name, tp) ->
    let tp' = refresh_tvars env tp in
    EExtern (name, tp') ,tp', EffPure

  | ETFn (a, body) ->
    let env, b = Env.extend_tvar env a in
    let body', tp, eff = transform_expr env body in
    ETFn (b, body'), TForallT(b, tp), eff

  | ETApp (e, tps) ->
    begin match transform_expr env e with
    | e', TForallT(args, body), eff when List.length args = List.length tps ->
      let tps = List.map (refresh_tvars env) tps in
      ETApp (e', tps),
      subst_list body args tps,
      eff
    | _ -> failwith "Internal type error"
    end

  | ELet (x, e1, e2) ->
    let e1', tp1, eff1 = transform_expr env e1 in
    let env = Env.add_var env x tp1 in
    let e2', tp2, eff2 = transform_expr env e2 in
    ELet (x, e1', e2'), tp2, Effect.join eff1 eff2

  | EPair (e1, e2) ->
    let e1', tp1, eff1 = transform_expr env e1 in
    let e2', tp2, eff2 = transform_expr env e2 in
    EPair (e1', e2'), TPair (tp1, tp2), Effect.join eff1 eff2

  | EFst e ->
    begin match transform_expr env e with
    | e', TPair (tp1, _), eff ->
      EFst e', tp1, eff
    | _ -> failwith "internal type error"
    end

  | ESnd e ->
    begin match transform_expr env e with
    | e', TPair (_, tp2), eff ->
      ESnd e', tp2, eff
    | _ -> failwith "internal type error"
    end

  | EIf (e1, e2, e3) ->
    let e1', tp1, eff1 = transform_expr env e1 in
    let e2', tp2, eff2 = transform_expr env e2 in
    let e3', tp3, eff3 = transform_expr env e3 in
    EIf (e1', e2', e3'), tp2, Effect.join eff1 (Effect.join eff2 eff3)

  | ESeq (e1, e2) ->
    let e1', tp1, eff1 = transform_expr env e1 in
    let e2', tp2, eff2 = transform_expr env e2 in
    ESeq (e1', e2'), tp2, Effect.join eff1 eff2

  | EType (alias, tvars, ctor_defs, body) ->
    let env, tvars' = Env.extend_tvar env tvars in
    let env = Env.extend_ctors env ctor_defs alias tvars in
    let body', tp, eff = transform_expr env body in
    EType (alias, tvars, ctor_defs, body'), tp, eff

  | ECtor (name, body) ->
    let expected, alias, tvars = Env.lookup_ctor env name in
    let body', tp, eff = transform_expr env body in
    let adt_args = Subst.get_subst (Env.tvar_set env) expected tp |> List.map snd in
    ECtor (name, body'),
    TADT (alias, adt_args), eff

  | EMatch (body, clauses, tp) ->
    let tp = refresh_tvars env tp in
    let body', body_tp, _ = transform_expr env body in
    let clauses' = match body_tp with
    | TADT(alias, args) ->
      let f (ctor, x, e) =
        let expected, alias', tvars = Env.lookup_ctor env ctor in
        let substituted = Subst.subst_list expected tvars args in
        let env = Env.add_var env x substituted in
        let e', tp, _ = transform_expr env e in
        (ctor, x, e')
      in
      List.map f clauses
    | TEmpty ->
      assert(List.length clauses = 0);
      []
    | _ -> failwith "internal type error"
    in EMatch (body', clauses', tp), tp, EffImpure

(** Setup application to match conditions presented in EnsureWellTyped

   Takes in environment,
    transformed expression e1' (with type and effect)
    list of transformed expressions es' (with effect)
  *)
and transform_app env (e1', tp1, eff1) es' =

  let rec inner1 acc es' tp eff =
    match es', tp with
    | es', TArrow(arr, _, _) when Arrow.view_eff arr = EffImpure ->
      List.rev acc, es', tp, eff
    | (e', eff') :: es', TArrow(arr, _, tres) ->
      inner1 (e'::acc) es' tres (Effect.join eff eff')
    | [], _ -> List.rev acc, [], tp, eff
    | _::_, _ ->
      Utils.report_internal_error "Application with too many arguments"

  and inner2 es' tp eff =
    match es', tp with
    | (e', eff') :: es', TArrow(_, _, tres) ->
      e', es', tres, Effect.join eff eff'
    | [], _ -> failwith "impossible"
    | _, _ -> failwith "internal type error"

  and inner3 acc es' tp =
    match es', tp with
    | (e', eff') :: es', TArrow(_, _, tres) when eff' = Effect.EffPure ->
      inner3 (e'::acc) es' tres
    | [], _ -> List.rev acc, [], tp
    | es', tp ->
      List.rev acc, es', tp

  in
  let part1, rest, tp, eff = inner1 [] es' tp1 eff1 in
  if List.is_empty rest
  (* if this list is empty whole application was pure *)
  then EApp(e1', part1), tp, eff
  else
    let part2, rest, tp, eff = inner2 rest tp eff in
    let part3, rest, tp = inner3 [] rest tp in
    let res = EApp(e1', part1 @ [part2] @ part3), tp, eff in
    if List.is_empty rest then res
    else transform_app env res rest

let transform_with_effects (p, env) =
  let start_env = Env.with_name_map env in
  let _ = fill_effects start_env p in
  let p, _, _ = transform_expr start_env p in
  p, env
