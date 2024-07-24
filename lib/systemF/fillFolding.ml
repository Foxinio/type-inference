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
    let adt_args = Subst.get_subst (Env.tvar_set env) expected tp
      |> List.map snd in
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
    | _ :: _, _ ->
      Utils.report_internal_error "Application with too many arguments"
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

(* used to compare arrows, if type is not an arrow, function returnes 0 *)
let arg_length tp =
  let rec inner acc = function
    | TArrow(_, _, tp) -> inner (acc+1) tp
    | _ -> acc
  in inner 0 tp

let minor_append x xs =
  match xs with
  | [] -> [[x]]
  | [] :: xss -> [x] :: xss
  | xs :: xss -> (x :: xs) :: xss

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

let destruct_tarrow = function
  | TArrow(arr, targ, tres) -> arr, targ, tres
  | _ -> failwith "internal error"

let make_wrapper env e' (eff : Effect.t) =
  match eff with
  | EffPure -> Fun.id, e'
  | EffImpure ->
    let x' = Env.fresh_var env in
    (fun e2 -> ELet(x', e', e2)), EVar x'

let rec unfold_app e' = function
  | [] -> e'
  | x :: xs -> unfold_app (EApp(e', List.rev x)) xs

let rec transform_expr env e : expr * tp * Effect.t =
  match e with
  | EUnit -> e, TUnit, EffPure
  | EBool _ -> e, TBool, EffPure
  | ENum _ -> e, TInt, EffPure
  | EVar x -> EVar x, Env.lookup_var env x, EffPure

  | EFn (xs, body, tp) ->
    let tp' = refresh_tvars env tp in
    let _, env, _ = Env.extend_var env xs tp' in
    let body', _, _  = transform_expr env body in
    let xs, body' = split_arrow body' xs tp' in
    EFn (xs, body', tp'), tp', EffPure

  | EFix (f, xs, body, tp) ->
    let tp' = refresh_tvars env tp in
    let _, env, _ = Env.extend_var env xs tp' in
    let body', _, _ = transform_expr (Env.add_var env f tp') body in
    let xs, body' = split_arrow body' xs tp' in
    EFix (f, xs, body', tp'), tp', EffPure

  | EApp (e1, es) ->
    let e1', tp, eff = transform_expr env e1 in
    transform_app env e1' es tp eff

  | EExtern (name, tp) ->
    let tp' = refresh_tvars env tp in
    EExtern (name, tp'), tp', EffPure

  | ETFn (a, body) ->
    let env, b = Env.extend_tvar env a in
    let body', tp, eff = transform_expr env body in
    ETFn (b, body'), TForallT(b, tp), eff

  | ETApp (e, tps) ->
    begin match transform_expr env e with
    | e', TForallT(args, body), eff ->
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
    let e1', _, eff1 = transform_expr env e1 in
    let e2', tp, eff2 = transform_expr env e2 in
    let e3', _, eff3 = transform_expr env e3 in
    EIf (e1', e2', e3'), tp, Effect.join eff1 (Effect.join eff2 eff3)

  | ESeq (e1, e2) ->
    let e1', _, eff1 = transform_expr env e1 in
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
    let adt_args = Subst.get_subst (Env.tvar_set env) expected tp
      |> List.map snd in
    ECtor (name, body'), TADT (alias, adt_args), eff

  | EMatch (body, clauses, tp) ->
    let tp = refresh_tvars env tp in
    let body', body_tp, eff = transform_expr env body in
    let clauses', eff' = match body_tp with
    | TADT(alias, args) ->
      let f (ctor, x, e) =
        let expected, alias', tvars = Env.lookup_ctor env ctor in
        let substituted = Subst.subst_list expected tvars args in
        let env = Env.add_var env x substituted in
        let e', tp, _ = transform_expr env e in
        (ctor, x, e')
      in
      List.map f clauses, Effect.EffImpure
    | TEmpty -> [], Effect.EffPure
    | _ -> failwith "internal type error"
    in EMatch (body', clauses', tp), tp, Effect.join eff eff'

(** Setup application to match conditions presented in EnsureWellTyped

   Takes in environment,
    transformed expression e1' (with type and effect)
    list of transformed expressions es' (with effect)
  *)
and transform_app env e1' es tp eff =
  let curring es tp eff =
    let rec generate_args args xs = function
      | TArrow(arr, _, tres) when Arrow.view_fold arr = FldFolded ->
        let x = Env.fresh_var env in
        generate_args (EVar x :: args) (x :: xs) tres
      | tp ->
      let rec generate_lets lets args' eff = function
        | (e, eff') :: rest when eff' = Effect.EffImpure ->
          let x = Env.fresh_var env in
          generate_lets ((x, e) ::lets) (EVar x::args')
            (Effect.join eff eff') rest
        | (e, _) :: rest ->
          generate_lets lets (e::args') eff rest
          (* lets are in reverse order,
              but instead of List.rev we will fold_left *)
        | [] ->
          lets, List.rev_append args' args, xs, eff
      in generate_lets [] [] eff es
    in generate_args [] [] tp
  in
  let rec uncurring acc es tp =
    match es, tp with

    | [e], TArrow(arr, targ, tres) when Arrow.view_fold arr = FldUnfolded ->
      let e', eff' = coerse_argument env e targ in
      let eff'', args = List.fold_left
        (fun (eff, acc) (e, eff') -> Effect.join eff eff', e :: acc)
        (eff,[])
        ((e', eff') :: acc) in
      EApp(e1', args), tres, eff''

    | [e], TArrow(arr, targ, tres) ->
      let e', eff' = coerse_argument env e targ in
      let e1wrapper, e1'' = make_wrapper env e1' eff in
      let lets, args, xs, eff'' = curring ((e', eff') :: acc) tp eff in
      let curried = EFn(xs, EApp(e1'', args), tres) in
      let lets = List.fold_left
          (fun e (x, e1) -> ELet(x, e1, e)) curried lets in
      e1wrapper lets, tres, eff''

    | e :: es, TArrow(arr, targ, tres) when Arrow.view_fold arr = FldFolded ->
      let e', eff' = coerse_argument env e targ in
      uncurring ((e',eff') :: acc) es tres

    | es, tp ->
      let eff', acc = List.fold_left
        (fun (eff, acc) (e, eff') -> Effect.join eff eff', e :: acc)
        (eff,[])
        acc in
      transform_app env (EApp (e1', acc)) es tp eff'

  in uncurring [] es tp

(* TODO Check correctness *)
(* ASK this is conceptually incorrect *)
and coerse_argument env e expected =
  let e', actual, eff = transform_expr env e in
  if arg_length actual = arg_length expected then e', eff else
  let ewrapper, e' = make_wrapper env e' eff in
  let rec inner1 e' tret =
    let rec inner2 xs eff vars actual expected =
      let arr1, _, actual   = destruct_tarrow actual in
      let arr2, _, expected = destruct_tarrow expected in
      match Arrow.view_fold arr1, Arrow.view_fold arr2 with

      (* e: (_, ...->)-> *)
      (* e': _, ...->    *)
      | FldFolded, FldFolded ->
        let x = Env.fresh_var env in
        let eff' = Effect.join eff @@ Arrow.view_eff arr1 in
        inner2 (x :: xs) eff' (minor_append (EVar x) vars) actual expected

      (* e: (_, ...->)-> *)
      (* e': _->...->    *)
      | FldUnfolded, FldFolded ->
        let x = Env.fresh_var env in
        let eff' = Effect.join eff @@ Arrow.view_eff arr1 in
        inner2 (x :: xs) eff' ([(EVar x)] :: vars) actual expected

      (* e: (_->...->)-> *)
      (* e': _, ...->    *)
      | FldFolded, FldUnfolded ->
        let x = Env.fresh_var env in
        let eff' = Effect.join eff @@ Arrow.view_eff arr1 in
        let xs, vars = x :: xs, minor_append (EVar x) vars in
        if eff' = EffPure then
          let body = inner1 e' expected vars actual expected in
          EFn(List.rev xs, body, tret)
        else
          let x' = Env.fresh_var env in
          let body = inner1 (EVar x') expected [List.hd vars] actual expected in
          let body' = ELet(x', unfold_app e' (List.rev @@ List.tl vars), body) in
          EFn(List.rev xs, body', tret)

      (* e: (_->...->)-> *)
      (* e': _->...->    *)
      | FldUnfolded, FldUnfolded ->
        let x = Env.fresh_var env in
        let _ = Effect.join eff @@ Arrow.view_eff arr1 in
        let xs, vars = x :: xs, minor_append (EVar x) vars in
        EFn(List.rev xs, unfold_app e' (List.rev vars), tret)

    in inner2 [] EffPure
  in
  inner1 e' expected [] actual expected |> ewrapper, eff


let transform_with_folding (p, env) =
  let start_env = Env.with_name_map env in
  let _ = fill_unfolds start_env p in
  let p, _, _ = transform_expr start_env p in
  p, env
