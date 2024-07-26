module Arrow = SystemF.Arrow
open Core
open Typing

let rec tr_type env (tp : Type.t) : SystemF.tp =
  let open Type in
  match view tp with
  | TUVar _ ->
    failwith "Unification variable unrealized"
  | TUnit -> SystemF.TUnit
  | TEmpty -> SystemF.TEmpty
  | TBool -> SystemF.TBool
  | TInt  -> SystemF.TInt
  | TVar x -> SystemF.TVar (Env.lookup_tvar env x)
  | TArrow(targ, tres) ->
    let arvar = Arrow.fresh () in
    SystemF.TArrow(arvar, tr_type env targ, tr_type env tres)
  | TPair(tp1, tp2) ->
    SystemF.TPair(tr_type env tp1, tr_type env tp2)
  | TADT(a, _, tps) ->
    SystemF.TADT(a, List.map (tr_type env) tps)

let tr_poly_typ env typ =
  let tp = Schema.get_template typ
  and args = Schema.get_arguments typ |> TVarSet.to_list in
  if List.is_empty args then tr_type env tp, env, [] else
  let env, args' = Env.extend_tvar env args in
  SystemF.TForallT(args', tr_type env tp), env, args'

let tr_poly_var env (name,typ) =
  let tp, env, forall = tr_poly_typ env typ in
  (name, tp), env, forall

let tr_typ env typ =
  tr_type env @@ Schema.get_template typ

let tr_var env (name,typ) =
  name, tr_typ env typ

let rec mark_impure env = function
  | SystemF.TArrow(_, _, (TArrow (_,_,_) as tres)) -> mark_impure env tres
  | SystemF.TArrow(arr, _, _) -> Arrow.set_impure arr
  | tp -> Utils.report_internal_error "Expected TArrow: %s"
    (SystemF.PrettyPrinter.pp_type (Env.get_ctx env) tp)

let rec tr_expr env (e : Schema.typ Imast.expr) : SystemF.expr =
  match e.data with
  | Imast.EUnit -> SystemF.EUnit
  | Imast.EBool b -> SystemF.EBool b
  | Imast.ENum n -> SystemF.ENum n
  | Imast.EVar (name, tapp_args) ->
    let var = SystemF.EVar name in
    let template, xs = Env.lookup_var env name in
    Checks.check_arg_amount_correctness xs tapp_args;
    if List.is_empty xs then var else
    let tapp_args' = List.map (tr_typ env) tapp_args in
    SystemF.ETApp (var, tapp_args')

  | Imast.EExtern (name, eff, tp) ->
    let tp' = tr_typ env tp in
    if eff = Core.Effect.EffImpure then mark_impure env tp';
    SystemF.EExtern (name, tp')

  | Imast.EFn(x, body) ->
    let xs, env, body = fold_fn env e in
    let tp = tr_typ env e.typ in
    SystemF.EFn(xs, tr_expr env body, tp)

  | Imast.EFix(f, x, body) ->
    let f' = tr_var env f in
    let env = Env.add_var env f' in
    let xs, env, body = fold_fn env e in
    SystemF.EFix(fst f, xs, tr_expr env body, snd f')

  | Imast.EApp(e1, e2) ->
    let e2' = tr_expr env e2 in
    SystemF.EApp (tr_expr env e1, [e2'])

  | Imast.ELet(x, e1, e2) ->
    let x', env', tvars = tr_poly_var env x in
    let e1' = tr_expr env' e1 in
    let env = Env.add_var env x' in
    let e2' = tr_expr env e2 in
    if List.is_empty tvars
    then SystemF.ELet(fst x, e1', e2')
    else SystemF.ELet(fst x, SystemF.ETFn(tvars, e1'), e2')

  | Imast.EPair(e1, e2) ->
    SystemF.EPair(tr_expr env e1, tr_expr env e2)
  | Imast.EFst e ->
    SystemF.EFst (tr_expr env e)
  | Imast.ESnd e ->
    SystemF.ESnd (tr_expr env e)

  | Imast.EIf(e1, e2, e3) ->
    SystemF.EIf(tr_expr env e1, tr_expr env e2, tr_expr env e3)

  | Imast.ESeq(e1, e2) ->
    SystemF.ESeq(tr_expr env e1, tr_expr env e2)

  | Imast.EType ((alias, _), ((_, typ) :: _ as ctor_defs), rest) ->
    let env', tvars = Env.extend_tvar env
      @@ TVarSet.to_list
      @@ Schema.get_arguments typ in
    let ctor_defs' = List.map (tr_var env') ctor_defs in
    SystemF.EType(alias, tvars, ctor_defs', tr_expr env rest)
  | Imast.EType ((alias,_), [], rest) ->
    SystemF.EType(alias, [], [], tr_expr env rest)

  | Imast.ECtor (name, body) ->
    SystemF.ECtor (name, tr_expr env body)

  | Imast.ETypeAlias (_, _, rest) ->
    (* at this point this expr doesn't do anything *)
    tr_expr env rest

  | Imast.EMatch (sub_expr, clauses) ->
    let tp = Schema.get_template e.typ |> tr_type env in
    let f (ctor,(x,_),e) = ctor, x, tr_expr env e in
    let clauses' = List.map f clauses in
    SystemF.EMatch(tr_expr env sub_expr, clauses', tp)

and fold_fn env (body : Schema.typ Imast.expr) =
  let rec inner env acc (body : Schema.typ Imast.expr) =
    match body.data with
    | Imast.EFn (x, body) ->
      let x' = tr_var env x in
      let env = Env.add_var env x' in
      inner env (fst x'::acc) body
    | _ -> List.rev acc, env, body
  in match body.data with
  | Imast.EFn (x, body) ->
    let x' = tr_var env x in
    let env = Env.add_var env x' in
    let res, env, body = inner env [] body in
    fst x' :: res, env, body
  | Imast.EFix(_, x, body) ->
    let x' = tr_var env x in
    let env = Env.add_var env x' in
    let res, env, body = inner env [] body in
    fst x' :: res, env, body
  | _ -> failwith "ToSystemF.fold_fn called with wrong argument"

let tr_program ((p,env) : program) : SystemF.program =
  tr_expr Env.empty p, env

