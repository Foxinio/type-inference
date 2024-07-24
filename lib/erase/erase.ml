include Ast

let rec take_n tp n =
  match n, tp with
  | 0, tp -> tp
  | n, SystemF.TArrow(_, _, tres) -> take_n tres (n-1)
  | _ -> failwith "internal error"

let rec tr_expr env (e : SystemF.expr) : Ast.expr * SystemF.tp =
  match e with
  | EUnit -> EUnit, TUnit
  | EBool b -> EBool b, TBool
  | ENum n -> ENum n, TInt
  | EVar x -> EVar x, Env.lookup_var env x

  | EFn (xs, body, tp) ->
    let env = Env.extend_vars env xs tp in
    let body', _ = tr_expr env body in
    EFn (xs, body'), tp

  | SystemF.EFix (f, xs, body, tp) ->
    let env = Env.extend_vars env xs tp in
    let body', _ = tr_expr (Env.add_var env f tp) body in
    EFix (f, xs, body'), tp

  | EApp(EApp(EExtern (s, _), [e1]), [e2])
  | EApp(EExtern (s, _), [e1; e2])
      when s = "and" ->
    tr_expr env (EIf(e1, e2, EBool false))

  | EApp(EApp(EExtern (s, _), [e1]), [e2])
  | EApp(EExtern (s, _), [e1; e2])
      when s = "or" -> 
    tr_expr env (EIf(e1, EBool true, e2))

  | EApp(EExtern (s, _), [e]) ->
    let _, tp = tr_expr env e in
    SystemF.PrettyPrinter.pp_type
      (Env.get_ctx env) tp
      |> Builtin.printType,
    TUnit

  | EApp (e1, es) ->
    let e1', tp = tr_expr env e1 in
    let es', _ = List.map (tr_expr env) es |> List.split in
    EApp(e1', es'), take_n tp (List.length es')

  | ETFn (_, body) ->
    tr_expr env body

  | ETApp (e, _) ->
    tr_expr env e

  | ELet (x, e1, e2) ->
    let e1', tp1 = tr_expr env e1 in
    let env = Env.add_var env x tp1 in
    let e2', tp2 = tr_expr env e2 in
    ELet(x, e1', e2'), tp2

  | EExtern (s, tp) ->
    let arity = Builtin.get_arity tp in
    Builtin.lookup_builtin s arity, tp

  | EPair (e1, e2) ->
    let e1', tp1 = tr_expr env e1 in
    let e2', tp2 = tr_expr env e2 in
    EPair(e1', e2'), TPair(tp1, tp2)

  | EFst e ->
    let fn = Builtin.lookup_builtin "fst" [1] in
    begin match tr_expr env e with
    | arg, TPair(tp1, _) -> 
      EApp (fn, [arg]), tp1
    | _ -> failwith "internal error"
    end

  | ESnd e ->
    let fn = Builtin.lookup_builtin "snd" [1] in
    begin match tr_expr env e with
    | arg, TPair(_, tp2) ->  EApp (fn, [arg]), tp2
    | _ -> failwith "internal error"
    end

  | EIf (cond, then_branch, else_branch) ->
    let cond', _ = tr_expr env cond in
    let then_branch', tp = tr_expr env then_branch in
    let else_branch', _  = tr_expr env else_branch in
    EIf (cond', then_branch', else_branch'), tp

  | ESeq (e1, e2) ->
    let e1', _ = tr_expr env e1 in
    let e2', tp = tr_expr env e2 in
    ESeq (e1', e2'), tp

  | EType (alias, _, ctor_defs, body) ->
    let env = Env.extend_ctors env
      (List.to_seq ctor_defs |> Seq.unzip |> fst) alias in
    tr_expr env body

  | ECtor (ctor_name, body) ->
    let ctor_name', adt_var = Env.lookup_ctor env ctor_name in
    let body', _ = tr_expr env body in
    (* at this point only thing that matters is that it's adt
       not it's arguments *)
    ECtor (ctor_name', body'), TADT(adt_var, [])

  | EMatch (sub_expr, clauses, tp) ->
    let sub_expr', _ = tr_expr env sub_expr in
    let clauses' = tr_clauses env tp clauses in
    EMatch (sub_expr', clauses'), tp

and tr_clauses env tp = function
  | [] when tp = SystemF.TEmpty -> Array.init 0 Obj.magic
  | [] -> failwith "internal error"
  | clauses ->
    let f (ctor_name, x, body) =
      let ctor_name', _ = Env.lookup_ctor env ctor_name in
      let body', _ = tr_expr env body in
      (ctor_name', x, body')
    in let rec fill_clauses acc i = function
      | (ctor_name', _, _ as clause) :: clauses when i+1 = ctor_name' ->
        fill_clauses (clause :: acc) (i+1) clauses
      | [] -> List.rev acc
      | clauses ->
        let x = Core.Imast.IMAstVar.fresh () in
        let body = Ast.EApp(Builtin.fail "Match failure", [EUnit]) in
        fill_clauses ((i, x, body) :: acc) (i+1) clauses
    in
    List.map f clauses
    |> List.sort (fun (c1, _, _) (c2, _, _) -> compare c1 c2)
    |> fill_clauses [] 0
    |> List.map (fun (_, x, e) -> x,e)
    |> Array.of_list

let erase_type (p,env) =
  let env' = Env.with_name_map env in
  let erased, _ = tr_expr env' p in
  erased, env
