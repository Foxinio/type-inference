open Core
open Main
open Subst
open Order

(* TODO check type eq instead of subtyping in whole program *)
let assert_type_eq tp1 tp2 =
  if Order.type_equal tp1 tp2 then () else
  Utils.report_internal_error "At checking well-scoped type equality, failed"

let assert_subtype tp1 tp2 =
  if Order.subtype tp1 tp2 then () else
  Utils.report_internal_error "At checking well-scoped type subtyping, failed"

let assert_subeffect e eff1 eff2 =
  if Effect.compare eff1 eff2 <= 0 then () else
  Utils.report_internal_error ("At checking well-scoped effect subeffecting"
    ^^ ", failed. Expected %s, Actual %s in %s")
    (Effect.to_string eff2) (Effect.to_string eff1) (PrettyPrinter.pp_expr e)

(** Checks if type is well-scoped, and refresh its type variables according to
    the environment *)
let rec check_well_scoped env tp =
  match tp with
  | TUnit | TEmpty | TBool | TInt -> tp
  | TVar a -> TVar (Env.lookup_tvar env a)
  | TArrow(arr, targ, tres) ->
    TArrow(arr, check_well_scoped env targ, check_well_scoped env tres)
  | TForallT(a, tp) ->
    let env, b = Env.extend_tvar env a in
    TForallT(b, check_well_scoped env tp)
  | TPair(tp1, tp2) ->
    TPair(check_well_scoped env tp1, check_well_scoped env tp2)
  | TADT(a, tps) ->
    TADT(a, List.map (check_well_scoped env) tps)

let rec infer_type env e =
  match e with
  | EUnit   -> TUnit, Effect.EffPure
  | EBool _ -> TBool, EffPure
  | ENum _  -> TInt, EffPure
  | EVar x  -> Env.lookup_var env x, EffPure

  | EFn (args, body, tp) ->
    let tp' = check_well_scoped env tp in
    let tres, env, eff = Env.extend_var env args tp' in
    check_type_and_effect env body tres eff;
    tp', EffPure

  | EFix (f, args, body, tp) ->
    let tp' = check_well_scoped env tp in
    let env = Env.add_var env f tp' in
    let tres, env, eff = Env.extend_var env args tp' in
    check_type_and_effect env body tres eff;
    tp', EffPure

  | EApp (e1, es) ->
    let tp1, eff = infer_type env e1 in
    let tres, eff = check_app_correctness env es tp1 eff in
    tres, eff

  | ETFn(a, body) ->
    let env, b = Env.extend_tvar env a in
    let tp, eff = infer_type env body in
    TForallT(b, tp), eff

  | ETApp(e, tps) ->
    begin match infer_type env e with
    | TForallT(args, body), eff when List.length args = List.length tps ->
      let tps = List.map (check_well_scoped env) tps in
      subst_list body args tps, eff
    | _ -> failwith "Internal type error"
    end

  | ELet(x, e1, e2) ->
    let tp1, eff1 = infer_type env e1 in
    let tp2, eff2 = infer_type (Env.add_var env x tp1) e2 in
    tp2, Effect.join eff1 eff2

  | EExtern(_, tp) ->
    check_well_scoped env tp, EffPure

  | EPair(e1, e2) ->
    let tp1, eff1 = infer_type env e1 in
    let tp2, eff2 = infer_type env e2 in
    TPair(tp1, tp2), Effect.join eff1 eff2

  | EFst e ->
    begin match infer_type env e with
    | TPair (tp1, _), eff -> tp1, eff
    | _ -> failwith "Internal type error"
    end

  | ESnd e ->
    begin match infer_type env e with
    | TPair(_, tp2), eff -> tp2, eff
    | _ -> failwith "Internal type error"
    end

  | EIf(e1, e2, e3) ->
    let eff1 = check_type env e1 TBool in
    let tp, eff2 = infer_type env e2 in
    let eff3 = check_type env e3 tp in
    tp, Effect.join eff1 (Effect.join eff2 eff3)

  | ESeq(e1, e2) ->
    let eff1 = check_type env e1 TUnit in
    let tp, eff2 = infer_type env e2 in
    tp, Effect.join eff1 eff2

  | EType(alias, tvars, ctor_defs, body) ->
    let env, tvars = Env.extend_tvar env tvars in
    let env = Env.extend_ctors env ctor_defs alias tvars in
    infer_type env body

  | ECtor (name, body) ->
    let expected, alias, tvars = Env.lookup_ctor env name in
    let tp, eff = infer_type env body in
    let _, adt_args = Subst.get_subst (Env.tvar_set env) expected tp in
    TADT (alias, adt_args), eff

  | EMatch(body, defs, tp) ->
    let res_tp = check_well_scoped env tp in
    begin match infer_type env body with
    | TADT(alias, args), _ ->
      let f (ctor, x, e) =
        let expected, alias', tvars = Env.lookup_ctor env ctor in
        assert (Imast.IMAstVar.compare alias alias' = 0);
        let substituted = Subst.subst_list expected tvars args in
        let env = Env.add_var env x substituted in
        let _ = check_type env e res_tp in ()
      in
      List.iter f defs;
      res_tp, EffImpure
    | TEmpty, eff1 ->
      assert(List.length defs = 0);
      res_tp, eff1
    | _ -> failwith "internal type error"
    end



and check_type env e tp =
  let tp', eff' = infer_type env e in
  assert_subtype tp' tp;
  eff'

and check_type_and_effect env e tp eff =
  let tp', eff' = infer_type env e in
  assert_subtype tp' tp;
  assert_subeffect e eff' eff


(*
 * EApp(e1, es) has to match specyfic rules:
 *   For es = ep₁ @ (Option.to_list ei) @ ep₂
 *   and typeof(e1) = tp₁ ->ₚ ... ->ₚ tpₖ ->ᵢtpₖ₊₁ ->_ ... ->_ tpₙ ->_ ...
 *                    \____|ep₁|____/        \_____|ep₂|_____/
 *
 *  These condition must be met:
 *  1) effectof(EApp(e1, ep₁) = EffPure
 *     (ignoring effects of evaluating elements of ep₁ and e1)
 *  2) effectof(EApp(e1, ep₁ @ [ei]) = EffImpure
 *     (ignoring effect of evaluating of ei and e1)
 *  3) ∀k+1 ≤ j ≤ n, effectof(es[j]) = EffPure
 *     (not ignoring effects of evaluating elements of ep₁)
 *
 * In that way transformation will not affect the order of observable effects.
 *)
and check_app_correctness env args tp eff1 =

  (* inner1 will check (1) condition *)
  let rec inner1 args tp eff =
    match args, tp with
    | [], tres -> tres, eff
    | _, TArrow(arr, _, _) when Arrow.view_eff arr = EffImpure ->
      inner2 args tp
    | e :: args, TArrow(arr, targ, tres) ->
      let targ', eff' = infer_type env e in
      assert_subtype targ' targ;
      inner1 args tres (Effect.join eff eff')
    | _ :: _, _ ->
      Utils.report_internal_error "Application with too many arguments"

  (* inner2 will check (2) condition *)
  and inner2 args tp =
    (* because inner2 is only called in inner1
       once application is determined to be impure
       there is no need to pass effect along *)
    match args, tp with
    | e :: args, TArrow(arr, targ, tres) ->
      let targ', _ = infer_type env e in
      assert_subtype targ' targ;
      inner3 args tres
    | [], _ -> Utils.report_internal_error "Application with too few arguments"
    | _ :: _, _ ->
      Utils.report_internal_error "Application with too many arguments"

  (* inner3 will check (3) condition *)
  and inner3 args tp =
    (* because inner3 is only called in inner2 effect is known *)
    match args, tp with
    | e :: args, TArrow(_, targ, tres) ->
      let targ', eff' = infer_type env e in
      if eff' = EffImpure then
        Utils.report_internal_error
          "Application with impure effect. (3) condition broken.";
      assert_subtype targ' targ;
      inner3 args tres
    | [], tres -> tres, Effect.EffImpure
    | _ :: _, _ ->
      Utils.report_internal_error "Application with too many arguments"


  in inner1 args tp eff1

let ensure_well_typed p =
  let env = Env.empty in
  ignore @@ infer_type env p;
  if !LmConfig.print_env then (
    Printf.eprintf "Env: %s\n%!" (Env.pp_vars env));
  ()




