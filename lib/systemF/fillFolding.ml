open Core
open Main
open Subst

let refresh_tvars = EnsureWellTyped.check_well_scoped

(* ========================================================================= *)
(* Analysis *)

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

let rec fill_unfolds env e =
  let open Effect in
  match e with
  | EUnit   -> TUnit
  | EBool _ -> TBool
  | ENum _  -> TInt
  | EVar x  -> Env.lookup_var env x

  | EFn (args, body, tp) ->
    let tp' = refresh_tvars env tp in
    let tres, env, arr = extend_var env args tp' in
    Arrow.set_unfolded arr;
    fill_no_ret env body;
    tp'

  | EFix (f, args, body, tp) ->
    let tp' = refresh_tvars env tp in
    let env = Env.add_var env f tp' in
    let tres, env, arr = extend_var env args tp' in
    Arrow.set_unfolded arr;
    fill_no_ret env body;
    tp'

  | EApp (e1, es) ->
    let tp1 = fill_unfolds env e1 in
    fill_unfolds_in_app env es tp1

  | ETFn(a, body) ->
    let env, b = Env.extend_tvar env a in
    let tp = fill_unfolds env body in
    TForallT(b, tp)

  | ETApp(e, tps) ->
    begin match fill_unfolds env e with
    | TForallT(args, body) when List.length args = List.length tps ->
      let tps = List.map (refresh_tvars env) tps in
      subst_list body args tps
    | _ -> failwith "Internal type error"
    end

  | ELet(x, e1, e2) ->
    let tp1 = fill_unfolds env e1 in
    let env = Env.add_var env x tp1 in
    let tp2 = fill_unfolds env e2 in
    tp2

  | EExtern(_, tp) ->
    refresh_tvars env tp

  | EPair(e1, e2) ->
    let tp1 = fill_unfolds env e1 in
    let tp2 = fill_unfolds env e2 in
    TPair(tp1, tp2)

  | EFst e ->
    begin match fill_unfolds env e with
    | TPair (tp1, _) -> tp1
    | _ -> failwith "Internal type error"
    end

  | ESnd e ->
    begin match fill_unfolds env e with
    | TPair(_, tp2) -> tp2
    | _ -> failwith "Internal type error"
    end

  | EIf(e1, e2, e3) ->
    fill_no_ret env e1;
    let tp2 = fill_unfolds env e2 in
    fill_no_ret env e3;
    tp2

  | ESeq(e1, e2) ->
    fill_no_ret env e1;
    let tp = fill_unfolds env e2 in
    tp

  | EType(alias, tvars, ctor_defs, body) ->
    let env, tvars = Env.extend_tvar env tvars in
    let env = Env.extend_ctors env ctor_defs alias tvars in
    fill_unfolds env body

  | ECtor (name, body) ->
    let expected, alias, tvars = Env.lookup_ctor env name in
    let tp = fill_unfolds env body in
    let adt_args = Subst.get_subst (Env.tvar_set env) expected tp |> List.map snd in
    TADT (alias, adt_args)

  | EMatch(body, defs, tp) ->
    let tp' = refresh_tvars env tp in
    begin match fill_unfolds env body with
    | TADT(alias, args) ->
      let f (ctor, x, e) =
        let expected, alias', tvars = Env.lookup_ctor env ctor in
        let substituted = Subst.subst_list expected tvars args in
        let env = Env.add_var env x substituted in
        fill_no_ret env e
      in
      List.iter f defs;
      tp'
    | TEmpty ->
      tp'
    | _ -> failwith "internal type error"
    end

and fill_no_ret env e =
  let _ = fill_unfolds env e in
  ()

and fill_unfolds_in_app env args tp =
  let rec inner args tp arr =
    match args, tp with
    | [], tres -> arr, tres
    | e :: args, TArrow(arr, _, tres) ->
      fill_no_ret env e;
      inner args tres arr
    | _ :: _, _ -> Utils.report_internal_error "Application with too many arguments"
  in
  match args, tp with
  | e :: args, TArrow(arr, _, tres) ->
      fill_no_ret env e;
    let arr, tp = inner args tres arr in
    Arrow.set_unfolded arr;
    tp
  |  _ -> Utils.report_internal_error "Application with too many arguments"

(* ========================================================================= *)
(* Transformation *)



let rec split_arrow body xs tp =
  let rec inner acc xs tp =
    match xs, tp with
    | x :: xs, TArrow(arr, _, tp2) when Arrow.view_fold arr = FldFolded ->
      inner (x :: acc) xs tp2
    | [], tp -> List.rev acc, body
    | xs, tp ->
      let xs, body = split_arrow body xs tp in
      let body' = EFn (xs, body, tp) in
      List.rev acc, body'
  in inner [] xs tp

let rec transform_expr env e : expr * tp =
  match e with
  | EUnit -> e, TUnit
  | EBool _ -> e, TBool
  | ENum _ -> e, TInt
  | EVar x -> EVar x, Env.lookup_var env x

  | EFn (xs, body, tp) ->
    let tp' = refresh_tvars env tp in
    let _, env, _ = Env.extend_var env xs tp' in
    let body', _  = transform_expr env body in
    let xs, body' = split_arrow body' xs tp' in
    EFn (xs, body', tp'), tp'

  | EFix (f, xs, body, tp) ->
    let tp' = refresh_tvars env tp in
    let _, env, _ = Env.extend_var env xs tp' in
    let body', _ = transform_expr (Env.add_var env f tp') body in
    let xs, body' = split_arrow body' xs tp' in
    EFix (f, xs, body', tp'), tp'

  | EApp (e1, es) ->
    let e1', tp = transform_expr env e1 in
    transform_app env e1' es tp

  | EExtern (name, tp) ->
    let tp' = refresh_tvars env tp in
    EExtern (name, tp') ,tp'

  | ETFn (a, body) ->
    let env, b = Env.extend_tvar env a in
    let body', tp = transform_expr env body in
    ETFn (b, body'), TForallT(b, tp)

  | ETApp (e, tps) ->
    begin match transform_expr env e with
    | e', TForallT(args, body) ->
      let tps = List.map (refresh_tvars env) tps in
      ETApp (e', tps),
      subst_list body args tps
    | _ -> failwith "Internal type error"
    end

    | ELet (x, e1, e2) ->
    let e1', tp1 = transform_expr env e1 in
    let env = Env.add_var env x tp1 in
    let e2', tp2 = transform_expr env e2 in
    ELet (x, e1', e2'), tp2

  | EPair (e1, e2) ->
    let e1', tp1 = transform_expr env e1 in
    let e2', tp2 = transform_expr env e2 in
    EPair (e1', e2'), TPair (tp1, tp2)

  | EFst e ->
    begin match transform_expr env e with
    | e', TPair (tp1, _) ->
      EFst e', tp1
    | _ -> failwith "internal type error"
    end

  | ESnd e ->
    begin match transform_expr env e with
    | e', TPair (_, tp2) ->
      ESnd e', tp2
    | _ -> failwith "internal type error"
    end

  | EIf (e1, e2, e3) ->
    let e1', _ = transform_expr env e1 in
    let e2', tp = transform_expr env e2 in
    let e3', _ = transform_expr env e3 in
    EIf (e1', e2', e3'), tp

  | ESeq (e1, e2) ->
    let e1', _ = transform_expr env e1 in
    let e2', tp2 = transform_expr env e2 in
    ESeq (e1', e2'), tp2

  | EType (alias, tvars, ctor_defs, body) ->
    let env, tvars' = Env.extend_tvar env tvars in
    let env = Env.extend_ctors env ctor_defs alias tvars in
    let body', tp = transform_expr env body in
    EType (alias, tvars, ctor_defs, body'), tp

  | ECtor (name, body) ->
    let expected, alias, tvars = Env.lookup_ctor env name in
    let body', tp = transform_expr env body in
    let adt_args = Subst.get_subst (Env.tvar_set env) expected tp |> List.map snd in
    ECtor (name, body'),
    TADT (alias, adt_args)

  | EMatch (body, clauses, tp) ->
    let tp = refresh_tvars env tp in
    let body', body_tp = transform_expr env body in
    let clauses' = match body_tp with
    | TADT(alias, args) ->
      let f (ctor, x, e) =
        let expected, alias', tvars = Env.lookup_ctor env ctor in
        let substituted = Subst.subst_list expected tvars args in
        let env = Env.add_var env x substituted in
        let e', tp = transform_expr env e in
        (ctor, x, e')
      in
      List.map f clauses
    | TEmpty -> []
    | _ -> failwith "internal type error"
    in EMatch (body', clauses', tp), tp

(** Setup application to match conditions presented in EnsureWellTyped

   Takes in environment,
    transformed expression e1' (with type and effect)
    list of transformed expressions es' (with effect)
  *)
and transform_app env e1' es tp =
  let rec inner acc es tp =
    match es, tp with
    | e :: es, TArrow(arr, _, tres) when Arrow.view_fold arr = FldFolded ->
      let e', tp = transform_expr env e in
      inner (e' :: acc) es tres
    | [], tp -> EApp(e1', List.rev acc), tp
    | es, tp ->
      transform_app env (EApp (e1', List.rev acc)) es tp
  in inner [] es tp

let transform_with_folding (p, env) =
  let start_env = Env.with_name_map env in
  let _ = fill_unfolds start_env p in
  let p, _ = transform_expr start_env p in
  p, env
