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

let tr_typ env typ =
  tr_type env @@ Schema.get_template typ

let tr_var env (name,tp) =
  name, tr_typ env tp

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
  | Imast.EVar (name, tp) ->
    let xs = Subst.get_subst
      (Schema.get_template tp)
      (Schema.get_template e.typ)
      |> List.map (fun (_, tp) -> tr_type env tp) in
    SystemF.ETApp (SystemF.EVar name, xs)

  | Imast.EExtern (name, eff, tp) ->
    let tp' = tr_typ env tp in
    if eff = Core.Effect.EffImpure then mark_impure env tp';
    SystemF.EExtern (name, tp')

  | Imast.EFn(x, body) ->
    let x', tp = tr_var env x in
    let xs, body = fold_fn env body in
    let tp = tr_typ env e.typ in
    SystemF.EFn(x' :: xs, tr_expr env body, tp)

  | Imast.EFix(f, x, body) ->
    let f, tp = tr_var env f in
    let x', _ = tr_var env x in
    let xs, body = fold_fn env body in
    SystemF.EFix(f, x' :: xs, tr_expr env body, tp)

  | Imast.EApp(e1, e2) ->
    let e2' = tr_expr env e2 in
    SystemF.EApp (tr_expr env e1, [e2'])

  | Imast.ELet((x, tp), e1, e2) ->
    let env', tvars = Env.extend_tvar env
        @@ TVarSet.to_list
        @@ Schema.get_arguments tp in
    let e1' = tr_expr env' e1 in
    let e2' = tr_expr env e2 in
    SystemF.ELet(x, SystemF.ETFn(tvars, e1'), e2')

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

and fold_fn env body =
  let rec inner (body : Schema.typ Imast.expr) =
    match body.data with
    | Imast.EFn (x, body) ->
      let x', _ = tr_var env x in
      let xs, body' = inner body in
      x'::xs, body'
    | _ -> [], body
  in inner body

let tr_program ((p,env) : program) : SystemF.program =
  tr_expr Env.empty p, env

