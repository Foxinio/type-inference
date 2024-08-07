open Core
open Imast
include Main

let rec tr_type env node (t : Ast.expl_type) : expl_type =
    match t with
    | Ast.TUnit -> TUnit
    | Ast.TInt  -> TInt
    | Ast.TBool -> TBool
    | Ast.THole -> THole
    | Ast.TVar x -> TVar (Env.lookup_tvar env node x)
    | Ast.TAlias (x, ts) -> 
      let ts = List.map (tr_type env node) ts in
      let v = Env.lookup_tvar env node x in
      TAlias (v, ts)
    | Ast.TPair (tp1, tp2) ->
      TPair (tr_type env node tp1, tr_type env node tp2)
    | Ast.TArrow (targ, tres) ->
      TArrow (tr_type env node targ, tr_type env node tres)

let fresh_tvar env x =
  let v = VarTbl.fresh_var x in
  v, Env.add_tvar env x v

let fresh_var env e (x,t) =
  let v = VarTbl.fresh_var x in
  (v, tr_type env e t), Env.add_var env x v

let rec tr_expr env (e : Ast.expl_type Ast.expr) : expl_type expr =
  let data = tr_expr_data env e in
  let typ = tr_type env e e.typ in
  { e with data; typ }

and tr_expr_data env (e : Ast.expl_type Ast.expr) : expl_type expr_data =
    match e.data with
    | Ast.EUnit -> EUnit
    | Ast.EBool b -> EBool b
    | Ast.ENum  n -> ENum n
    | Ast.EVar (s,lst) ->
      EVar (Env.lookup_var env e s, List.map (tr_type env e) lst)
    | Ast.EExtern (s, eff, t) ->
      EExtern (s, eff, tr_type env e t)
    | Ast.EFn (x, e) ->
      let x', env = fresh_var env e x in
      let e = tr_expr env e in
      EFn (x', e)
    | Ast.EFix (f, x, e) ->
      let x', env = fresh_var env e x in
      let f', env = fresh_var env e f in
      let e = tr_expr env e in
      EFix (f', x', e)
    | Ast.EApp (e1, e2) ->
      let e1 = tr_expr env e1 in
      let e2 = tr_expr env e2 in
      EApp (e1, e2)
    | Ast.ELet (x, e1, e2) ->
      let e1 = tr_expr env e1 in
      let x', env = fresh_var env e x in
      let e2 = tr_expr env e2 in
      ELet (x', e1, e2)
    | Ast.EPair (e1, e2) ->
      let e1 = tr_expr env e1 in
      let e2 = tr_expr env e2 in
      EPair (e1, e2)
    | Ast.EFst e ->
      let e = tr_expr env e in
      EFst e
    | Ast.ESnd e ->
      let e = tr_expr env e in
      ESnd e
    | Ast.EIf (e1, e2, e3) ->
      let e1 = tr_expr env e1 in
      let e2 = tr_expr env e2 in
      let e3 = tr_expr env e3 in
      EIf (e1, e2, e3)
    | Ast.ESeq (e1, e2) ->
      let e1 = tr_expr env e1 in
      let e2 = tr_expr env e2 in
      ESeq (e1, e2)
    | Ast.ETypeAlias ((name, args), rhs, e) ->
      let delta_env', args' = Env.extend_delta env args in
      let rhs' = tr_type env e rhs in
      let name', env = fresh_tvar env name in
      let e' = tr_expr env e in
      ETypeAlias ((name', args'), rhs', e')
    | Ast.EType ((alias_name, alias_args), ctors, rest) ->
      let alias_name', env = fresh_tvar env alias_name in
      let env', alias_args' = Env.extend_delta env alias_args in
      let env, ctors' =
        List.map (fun (x, tp) -> x, tr_type env' e tp) ctors
        |> Env.extend_ctors env in
      let rest' = tr_expr env rest in
      EType((alias_name', alias_args'), ctors', rest')
    | Ast.ECtor (name, tps, e) ->
      let name' = Env.lookup_ctor env e name in
      let tps'  = List.map (tr_type env e) tps in
      let e' = tr_expr env e in
      ECtor (name', tps', e')
    | Ast.EMatch (e, clauses) ->
      let e' = tr_expr env e in
      let clauses' = List.map (tr_clauses env e) clauses in
      EMatch (e', clauses')

and tr_clauses env node (ctor_name, x, e) =
  let ctor_name' = Env.lookup_ctor env node ctor_name in
  let x', env = fresh_var env e x in
  let e' = tr_expr env e in
  (ctor_name', x', e')

let translate (p : Ast.program) : program =
  try tr_expr Env.empty p
  with Out_of_scope (s, node) ->
    let str = Ast.string_of_expr node Fun.id (fun _ -> "_") in
    Utils.report_error node "Undefined variable: %s in %s\n" s str

