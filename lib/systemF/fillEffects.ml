module Effect = Core.Effect
open Core.Imast
open Main
open Subst

let refresh_tvars = EnsureWellTyped.check_well_scoped

(* ========================================================================= *)
(* Analysis *)

let rec unify_subtypes env tp1 tp2 =
  match tp1, tp2 with
  | TUnit, TUnit
  | TEmpty, TEmpty
  | TBool, TBool
  | TInt, TInt -> ()
  | TVar x, TVar y when TVar.compare x y = 0 -> ()
  | TArrow(arr1, ta1, tb1), TArrow(arr2, ta2, tb2) ->
    Arrow.unify_uvar arr1 arr2;
    unify_subtypes env ta2 ta1;
    unify_subtypes env tb1 tb2

  | TForallT(a1, tp1), TForallT(a2, tp2) ->
    let lst = Seq.forever (fun () -> TVar(TVar.fresh ()))
      |> Seq.take (List.length a1)
      |> List.of_seq in
    begin try
        unify_subtypes env (subst_list tp1 a1 lst) (subst_list tp2 a2 lst)
      with Invalid_argument _ ->
        Utils.report_unbound_tvar ()
    end

  | TPair (tp1a, tp1b), TPair (tp2a, tp2b) ->
    unify_subtypes env tp1a tp2a;
    unify_subtypes env tp1b tp2b

  | TADT (x, args1), TADT (y, args2) when IMAstVar.compare x y = 0 ->
    assert (List.length args1 = List.length args2);
    List.iter2 (unify_eqtype env) args1 args2

  | (TUnit | TEmpty | TBool | TInt | TVar _  | TADT (_, _)
    | TArrow (_, _, _) | TPair(_, _) | TForallT (_, _)), _ ->
    Utils.report_type_missmatch tp1 tp2

and unify_eqtype env tp1 tp2 =
  unify_subtypes env tp1 tp2;
  unify_subtypes env tp2 tp1

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


let rec fill_effects env e arr =
  let open Effect in
  match e with
  | EUnit   -> TUnit
  | EBool _ -> TBool
  | ENum _  -> TInt
  | EVar x  -> Env.lookup_var env x

  | EFn (args, body, tp) ->
    let tp' = refresh_tvars env tp in
    let tres, env, arr' = extend_var env args tp' in
    check_type env body tres arr';
    tp'

  | EFix (f, args, body, tp) ->
    let tp' = refresh_tvars env tp in
    let env = Env.add_var env f tp' in
    let tres, env, arr' = extend_var env args tp' in
    Arrow.set_impure arr';
    check_type env body tres arr';
    tp'

  | EApp (e1, es) ->
    let tp1 = fill_effects env e1 arr in
    assert(not @@ List.is_empty es);
    fill_effects_in_app env es tp1 arr

  | ETFn(a, body) ->
    let env, b = Env.extend_tvar env a in
    let tp = fill_effects env body arr in
    TForallT(b, tp)

  | ETApp(e, tps) ->
    begin match fill_effects env e arr with
    | TForallT(args, body) when List.length args = List.length tps ->
      let tps = List.map (refresh_tvars env) tps in
      subst_list body args tps
    | actual -> Utils.report_unexpected_type actual "TForallT"
    end

  | ELet(x, e1, e2) ->
    let tp1 = fill_effects env e1 arr in
    let env = Env.add_var env x tp1 in
    let tp2 = fill_effects env e2 arr in
    tp2

  | EExtern(_, tp) ->
    refresh_tvars env tp

  | EPair(e1, e2) ->
    let tp1 = fill_effects env e1 arr in
    let tp2 = fill_effects env e2 arr in
    TPair(tp1, tp2)

  | EFst e ->
    begin match fill_effects env e arr with
    | TPair (tp1, _) -> tp1
    | actual -> Utils.report_unexpected_type actual "TPair"
    end

  | ESnd e ->
    begin match fill_effects env e arr with
    | TPair(_, tp2) -> tp2
    | actual -> Utils.report_unexpected_type actual "TPair"
    end

  | EIf(e1, e2, e3) ->
    check_type env e1 TBool arr;
    let tp2 = fill_effects env e2 arr in
    let tp3 = fill_effects env e3 arr in
    unify_eqtype env tp2 tp3;
    tp2

  | ESeq(e1, e2) ->
    check_type env e1 TUnit arr;
    fill_effects env e2 arr

  | EType(alias, tvars, ctor_defs, body) ->
    let env', tvars = Env.extend_tvar env tvars in
    let env = Env.extend_ctors env' ctor_defs alias tvars in
    fill_effects env body arr

  | ECtor (name, body) ->
    let expected, alias, tvars = Env.lookup_ctor env name in
    let tp = fill_effects env body arr in
    let _, adt_args = Subst.get_subst (Env.tvar_set env) expected tp in
    TADT (alias, adt_args)

  | EMatch(body, defs, tp) ->
    let tp' = refresh_tvars env tp in
    begin match fill_effects env body arr with
    | TADT(alias, args) ->
      let f (ctor, x, e) =
        let expected, alias', tvars = Env.lookup_ctor env ctor in
        assert (IMAstVar.compare alias alias' = 0);
        let substituted = Subst.subst_list expected tvars args in
        let env = Env.add_var env x substituted in
        check_type env e tp' arr
      in
      List.iter f defs;
      Arrow.set_impure arr;
      tp'
    | TEmpty ->
      assert(List.length defs = 0);
      tp'
    | actual -> Utils.report_unexpected_type actual "TADT or TEmpty"
    end

and check_type env e tp arr =
  let tp' = fill_effects env e arr in
  unify_subtypes env tp' tp

and fill_effects_in_app env args tp arr =
  let rec inner args tp arr =
    match args, tp with
    | [], tres -> tres
    | e :: args, TArrow(arr', targ, tres) ->
      let targ' = fill_effects env e arr in
      unify_subtypes env targ' targ;
      Arrow.unify_effect arr' arr;
      inner args tres arr
    | _ :: _, _ -> Utils.report_too_many_arguments ()
  in inner args tp arr

(* =========================================================================== *)
(* Crude analysis *)

let rec impure_type = function
  | TUnit | TEmpty | TBool | TInt | TVar _ -> ()
  | TForallT (_, tp) ->
    impure_type tp
  | TPair(tp1, tp2) ->
    impure_type tp1;
    impure_type tp2
  | TADT (_, args) ->
    List.iter impure_type args
  | TArrow (arr, tp1, tp2) ->
    Arrow.set_impure arr;
    impure_type tp1;
    impure_type tp2

let rec impure_expr = function
  | EUnit | EBool _ | ENum _ | EVar _ -> ()
  | EFn (_, body, tp) ->
    impure_type tp;
    impure_expr body
  | EFix (_, _, body, tp) ->
    impure_type tp;
    impure_expr body
  | EApp(e1, es) ->
    impure_expr e1;
    List.iter impure_expr es
  | ETFn (_, body) ->
    impure_expr body
  | ETApp(e, _) ->
    impure_expr e
  | ELet(x, e1, e2) ->
    impure_expr e1;
    impure_expr e2
  | EExtern (_, tp) ->
    impure_type tp
  | EPair(e1, e2) ->
    impure_expr e1;
    impure_expr e2
  | EFst e ->
    impure_expr e
  | ESnd e ->
    impure_expr e
  | EIf(e1, e2, e3) -> 
    impure_expr e1;
    impure_expr e2;
    impure_expr e3
  | ESeq(e1, e2) -> 
    impure_expr e1;
    impure_expr e2
  | EType (_, _, ctors, body) ->
    List.iter impure_ctors ctors;
    impure_expr body
  | ECtor (_, body) ->
    impure_expr body
  | EMatch(e, clauses, tp) ->
    impure_expr e;
    List.iter impure_clause clauses;
    impure_type tp

and impure_ctors = function
  | (_, tp) ->
    impure_type tp

and impure_clause = function
  | (_, _, e) ->
    impure_expr e

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
    | _, actual, _ -> Utils.report_unexpected_type actual "TForallT"
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
    | _, actual, _ -> Utils.report_unexpected_type actual "TPair"
    end

  | ESnd e ->
    begin match transform_expr env e with
    | e', TPair (_, tp2), eff ->
      ESnd e', tp2, eff
    | _, actual, _ -> Utils.report_unexpected_type actual "TPair"
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
    let _, adt_args = Subst.get_subst (Env.tvar_set env) expected tp in
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
    | actual -> Utils.report_unexpected_type actual "TADT or TEmpty"
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
      Utils.report_too_many_arguments ()

  and inner2 es' tp eff =
    match es', tp with
    | (e', eff') :: es', TArrow(_, _, tres) ->
      e', es', tres, Effect.join eff eff'
    | [], _ -> failwith "impossible"
    | _, actual -> Utils.report_unexpected_type actual "TArrow"

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

let transform_with_effects p =
  ignore @@ fill_effects Env.empty p (Arrow.fresh ());
  let p, _, _ = transform_expr Env.empty p in
  p

let crude_transform_with_effects p =
  impure_expr p;
  let p, _, _ = transform_expr Env.empty p in
  p
  
