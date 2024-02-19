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
                ({ data; typ; start_pos; end_pos } as node : Ast.expl_type Ast.expr) : expl_type expr =
    let rec extend_gamma (keys : Ast.expl_type Ast.var list) : IMAstVar.t StringMap.t * expl_type var list =
        let f (x,t) = 
          let v = IMAstVar.fresh () in
          VarTbl.add vartbl v x;
          Seq.return ((x, v), (v, Option.map (conv_type delta_env) t))
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
        (v, Option.map (conv_type delta_env) t)
    and conv_expr (e : Ast.expl_type Ast.expr_data) : expl_type expr_data =
      match e with
      | Ast.EUnit -> EUnit
      | Ast.EBool b -> EBool b
      | Ast.ENum  n -> ENum n
      | Ast.EVar (s,t) -> EVar (env_find node s gamma_env, Option.map (conv_type delta_env) t)
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
      | Ast.EInl e ->
        let e = inner gamma_env delta_env e in
        EInl e
      | Ast.EInr e ->
        let e = inner gamma_env delta_env e in
        EInr e
      | Ast.ECase (e, ((x1,t1),e1), ((x2,t2),e2)) ->
        let e = inner gamma_env delta_env e in
        let (v1,t1) = fresh_var (x1,t1) in
        let (v2,t2) = fresh_var (x2,t2) in
        let e1 = inner (StringMap.add x1 v1 gamma_env) delta_env e1 in
        let e2 = inner (StringMap.add x2 v2 gamma_env) delta_env e2 in
        ECase (e, ((v1,t1), e1), ((v2,t2), e2))
      | Ast.EIf (e1, e2, e3) ->
        let e1 = inner gamma_env delta_env e1 in
        let e2 = inner gamma_env delta_env e2 in
        let e3 = inner gamma_env delta_env e3 in
        EIf (e1, e2, e3)
      | Ast.ESeq (e1, e2) ->
        let e1 = inner gamma_env delta_env e1 in
        let e2 = inner gamma_env delta_env e2 in
        ESeq (e1, e2)
      | Ast.EAbsurd e ->
        let e = inner gamma_env delta_env e in
        EAbsurd e
      | Ast.ETypeAlias ((args, name), rhs, e) ->
        let delta_env', args' = extend_delta delta_env args in
        let rhs' = conv_type delta_env rhs in
        let name', _ = fresh_var (name,None) in
        let delta_env = StringMap.add name name' delta_env in
        let e' = inner gamma_env delta_env e in
        ETypeAlias ((args', name'), rhs', e')
      | Ast.EType ((scheme_args, scheme_name), ctor_list, rest) ->
        let scheme_name', _ = fresh_var (scheme_name, None) in
        let delta_env_with_scheme_name = StringMap.add scheme_name scheme_name' delta_env in
        let delta_env_with_scheme_args, scheme_args' = extend_delta delta_env_with_scheme_name scheme_args in
        let f (ctor_name, ctor_type) = 
          let ctor_name' = IMAstVar.fresh () in
          VarTbl.add vartbl ctor_name' ctor_name;
          Seq.return ((ctor_name, ctor_name'),
            (ctor_name', conv_type delta_env_with_scheme_args ctor_type))
        in
        let delta_env, ctor_list' = extend_map f ctor_list delta_env_with_scheme_name in
        let rest' = inner gamma_env delta_env rest in
        EType((scheme_args', scheme_name'), ctor_list', rest')
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
        | Ast.TSchema (ts, x) -> 
          let ts = List.map (conv_type delta_env) ts in
          let v = env_find node x delta_env in
          TSchema (ts, v)
        | Ast.TProd ts ->
          TProd (List.map (conv_type delta_env) ts)
        | Ast.TCoProd ts ->
          TCoProd (List.map (conv_type delta_env) ts)
        | Ast.TArrow (ts, t) ->
          TArrow (List.map (conv_type delta_env) ts, (conv_type delta_env) t)
    in
    { data = conv_expr data
    ; typ  = Option.map (conv_type delta_env) typ
    ; start_pos
    ; end_pos 
    }
  in 
  try inner StringMap.empty StringMap.empty p, vartbl
  with Out_of_scope (s, node) ->
    Utils.report_error node "Undefined variable: %s\n" s
    
    
