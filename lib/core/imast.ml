module IMAstVar = Tvar.Make()
module VarTbl = IMAstVar.MakeHashtbl()

include Ast.Make(struct
  type t = IMAstVar.t
end)

type program = expl_type expr * string VarTbl.t

exception Out_of_scope of string * Ast.expl_type Ast.expr

module StringMap = Map.Make(String)
let env_find e x env =
    match StringMap.find_opt x env with
    | Some v -> v
    | None -> raise (Out_of_scope (x, e))

let extend_map f keys env =
    let seq = List.to_seq keys |> Seq.flat_map f |> Seq.unzip in
    StringMap.add_seq (fst seq) env, List.of_seq (snd seq)


(** convert Ast.expr to expr *)
let translate_to_IMAst (p : Ast.program) : program =
  let vartbl : string VarTbl.t = VarTbl.create 11 in
  let rec inner (gamma_env : IMAstVar.t StringMap.t)
                (delta_env : IMAstVar.t StringMap.t)
                ({ data; typ; _ } as node : Ast.expl_type Ast.expr) : expl_type expr =
    let rec extend_gamma (keys : Ast.expl_type Ast.var list) : IMAstVar.t StringMap.t * expl_type var list =
        let f (x,t) = 
          let v = IMAstVar.fresh () in
          VarTbl.add vartbl v x;
          Seq.return ((x, v), (v, conv_type delta_env t))
        in
          extend_map f keys gamma_env
    and extend_delta delta_env (keys : Ast.var_type list) : IMAstVar.t StringMap.t * var_type list =
        let f x = 
          let v = IMAstVar.fresh () in
          VarTbl.add vartbl v x;
          Seq.return ((x, v), v)
        in
        extend_map f keys delta_env
    and fresh_var (x,t) =
        let v = IMAstVar.fresh () in
        VarTbl.add vartbl v x;
        (v, conv_type delta_env t)
    and conv_expr (e : Ast.expl_type Ast.expr_data) : expl_type expr_data =
      match e with
      | Ast.EUnit -> EUnit
      | Ast.EBool b -> EBool b
      | Ast.ENum  n -> ENum n
      | Ast.EVar (s,t) -> EVar (env_find node s gamma_env, conv_type delta_env t)
      | Ast.EFn (xs, e) ->
        let gamma_env, xs = extend_gamma xs in
        let e = inner gamma_env delta_env e in
        EFn (xs, e)
      | Ast.EFix ((f,t), xs, e) ->
        let gamma_env, xs = extend_gamma xs in
        let (fv,t) = fresh_var (f,t) in
        let gamma_env = StringMap.add f fv gamma_env in
        let e = inner gamma_env delta_env e in
        EFix ((fv,t), xs, e)
      | Ast.EApp (e1, es) ->
        let e1 = inner gamma_env delta_env e1 in
        let es = List.map (inner gamma_env delta_env) es in
        EApp (e1, es)
      | Ast.ELet ((x,t), e1, e2) ->
        let e1 = inner gamma_env delta_env e1 in
        let (v,t) = fresh_var (x,t) in
        let gamma_env = StringMap.add x v gamma_env in
        let e2 = inner gamma_env delta_env e2 in
        ELet ((v,t), e1, e2)
      | Ast.EPair (e1, e2) ->
        let e1 = inner gamma_env delta_env e1 in
        let e2 = inner gamma_env delta_env e2 in
        EPair (e1, e2)
      | Ast.EFst e ->
        let e = inner gamma_env delta_env e in
        EFst e
      | Ast.ESnd e ->
        let e = inner gamma_env delta_env e in
        ESnd e
      | Ast.EIf (e1, e2, e3) ->
        let e1 = inner gamma_env delta_env e1 in
        let e2 = inner gamma_env delta_env e2 in
        let e3 = inner gamma_env delta_env e3 in
        EIf (e1, e2, e3)
      | Ast.ESeq (e1, e2) ->
        let e1 = inner gamma_env delta_env e1 in
        let e2 = inner gamma_env delta_env e2 in
        ESeq (e1, e2)
      | Ast.ETypeAlias ((name, args), rhs, e) ->
        let delta_env', args' = extend_delta delta_env args in
        let rhs' = conv_type delta_env rhs in
        let name', _ = fresh_var (name,THole) in
        let delta_env = StringMap.add name name' delta_env in
        let e' = inner gamma_env delta_env e in
        ETypeAlias ((name', args'), rhs', e')
      | Ast.EType ((alias_name, alias_args), ctor_list, rest) ->
        let alias_name', _ = fresh_var (alias_name, THole) in
        let delta_env_with_alias_name = StringMap.add alias_name alias_name' delta_env in
        let delta_env_with_alias_args, alias_args' = extend_delta delta_env_with_alias_name alias_args in
        let f (ctor_name, ctor_type) = 
          let ctor_name' = IMAstVar.fresh () in
          VarTbl.add vartbl ctor_name' ctor_name;
          Seq.return ((ctor_name, ctor_name'),
            (ctor_name', conv_type delta_env_with_alias_args ctor_type))
        in
        let delta_env, ctor_list' = extend_map f ctor_list delta_env_with_alias_name in
        let rest' = inner gamma_env delta_env rest in
        EType((alias_name', alias_args'), ctor_list', rest')
      | Ast.ECtor (name, e) ->
        let name' = env_find node name delta_env in
        let e' = inner gamma_env delta_env e in
        ECtor (name', e')
      | Ast.EMatch (e, clauses) ->
        let f (ctor_name, (x,t), e) =
          let ctor_name' = env_find node ctor_name delta_env in
          let (x',t') = fresh_var (x,t) in
          let gamma_env = StringMap.add x x' gamma_env in
          let e' = inner gamma_env delta_env e in
          (ctor_name', (x',t'), e')
        in 
        let e' = inner gamma_env delta_env e in
        let clauses' = List.map f clauses in
        EMatch (e', clauses')
    and conv_type delta_env (t : Ast.expl_type) : expl_type =
        match t with
        | Ast.TUnit -> TUnit
        | Ast.TInt  -> TInt
        | Ast.TBool -> TBool
        | Ast.THole -> THole
        | Ast.TVar x -> TVar (env_find node x delta_env)
        | Ast.TAlias (x, ts) -> 
          let ts = List.map (conv_type delta_env) ts in
          let v = env_find node x delta_env in
          TAlias (v, ts)
        | Ast.TPair (tp1, tp2) ->
          TPair (conv_type delta_env tp1, conv_type delta_env tp2)
        | Ast.TArrow (ts, t) ->
          TArrow (List.map (conv_type delta_env) ts, (conv_type delta_env) t)
    in
    { node with
      data = conv_expr data;
      typ  = conv_type delta_env typ
    }
  in 
  try inner StringMap.empty StringMap.empty p, vartbl
  with Out_of_scope (s, node) ->
    Utils.report_error node "Undefined variable: %s\n" s


