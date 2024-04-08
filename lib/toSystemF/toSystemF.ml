open Core
open Imast

module SystemF = System_f.Type
open Typing

let rec tr_type env (tp : Type.t) : SystemF.tp =
  let open Type in
  match view tp with
  | TUVar _ | TGVar _ ->
    failwith "Unification variable unrealized"
  | TUnit -> SystemF.TUnit
  | TEmpty -> SystemF.TEmpty
  | TBool -> SystemF.TBool
  | TInt  -> SystemF.TInt
  | TVar x -> SystemF.TVar (Env.lookup_tvar env x)
  | TArrow(tps, tp) ->
    SystemF.TArrow(List.map (tr_type env) tps, tr_type env tp)
  | TProd(tps) ->
    SystemF.TProd(List.map (tr_type env) tps)
  | TADT(a, _, tps) ->
    SystemF.TADT(a, List.map (tr_type env) tps)

let tr_var env (name,tp) =
  name, tr_type env @@ Schema.get_template tp

let rec tr_expr env (e : Schema.typ expr) : SystemF.expr =
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

  | Imast.EFn(xs, e) ->
    let lst = List.map (tr_var env) xs in
    SystemF.EFn(lst, tr_expr env e)

  | Imast.EFix(f, xs, body) ->
    let f, _ = tr_var env f in
    let lst = List.map (tr_var env) xs in
    let tpres = tr_type env @@ Schema.get_template body.typ in
    SystemF.EFix(f, lst, tpres, tr_expr env e)

  | Imast.EApp(e1, es) ->
    SystemF.EApp (tr_expr env e1, List.map (tr_expr env) es)

  | Imast.ELet((x, tp), e1, e2) ->
    let env', tvars = Env.extend_tvar env @@ TVarSet.to_list @@ Schema.get_arguments tp in
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
    let env', tvars = Env.extend_tvar env @@ TVarSet.to_list @@ Schema.get_arguments typ in
    let ctor_defs' = List.map (tr_var env') ctor_defs in
    let tvars' = List.map (fun a -> SystemF.TVar a) tvars in
    let adt_t = SystemF.TForallT (tvars, SystemF.TADT (alias, tvars')) in
    SystemF.EType(adt_t, ctor_defs', tr_expr env rest)
  | Imast.EType ((alias,_), [], rest) ->
    SystemF.EType(SystemF.TADT(alias,[]), [], tr_expr env rest)

  | Imast.ECtor (name, body) ->
    SystemF.ECtor (name, tr_expr env body)

  | Imast.ETypeAlias (alias, typ, rest) ->
    (* at this point this expr doesn't do anything *)
    tr_expr env rest

  | Imast.EMatch (sub_expr, clauses) ->
    let tp = Schema.get_template sub_expr.typ |> tr_type env in
    let f (ctor,(x,_),e) = ctor, x, tr_expr env e in
    let clauses' = List.map f clauses in
    SystemF.EMatch(tr_expr env sub_expr, tp, clauses')


let tr_program ((p,_) : program) : SystemF.program =
  tr_expr Env.empty p
