include Ast



let rec tr_expr env e =
  match e with
  | SystemF.EUnit ->
    make EUnit
	| SystemF.EBool b ->
    make (EBool b)
	| SystemF.ENum n ->
    make (ENum n)
	| SystemF.EVar x ->
    make (EVar x)
	| SystemF.ECoerse (c, e) ->
    (* TODO: something might be needed to be done here *)
    tr_expr env e
	| SystemF.EFn (xs, body) ->
    let xs' = List.map fst xs in
    let body' = tr_expr env body in
    make (EFn (xs', body'))
	| SystemF.EFix (f, xs, _, body) ->
    let xs' = List.map fst xs in
    let body' = tr_expr env body in
    make (EFix (f, xs', body'))
  | SystemF.EApp(SystemF.EExtern (s, _, _), [e1; e2])
      when s = "and" ->
    let open SystemF in
    tr_expr env (EIf(e1, e2, EBool false))
  | SystemF.EApp(SystemF.EExtern (s, _, _), [e1; e2])
      when s = "or" -> 
    let open SystemF in
    tr_expr env (EIf(e1, EBool true, e2))
	| SystemF.EApp (e, es) ->
    let es' = List.map (tr_expr env) es in
    let e'  = tr_expr env e in
    make (EApp (e', es'))
	| SystemF.ETFn (_, body) ->
    tr_expr env body
	| SystemF.ETApp (e, _) ->
    tr_expr env e
	| SystemF.ELet (x, e1, e2) ->
    let e1' = tr_expr env e1 in
    let e2' = tr_expr env e2 in
    make (ELet(x, e1', e2'))
	| SystemF.EExtern (s, _, tparg) ->
    begin match Builtin.lookup_builtin_opt s with
      | Some e -> make e
      | None when s = "printType" ->
        SystemF.PrettyPrinter.string_of_type tparg
          |> Builtin.printType
          |> make
      | None -> failwith "internal error"
    end
	| SystemF.EPair (e1, e2) ->
    let e1' = tr_expr env e1 in
    let e2' = tr_expr env e2 in
    make (EPair(e1', e2'))
	| SystemF.EFst e ->
    let fn = make @@ Builtin.lookup_builtin "fst" in
    let arg = tr_expr env e in
    make (EApp (fn, [arg]))
	| SystemF.ESnd e ->
    let fn = make @@ Builtin.lookup_builtin "snd" in
    let arg = tr_expr env e in
    make (EApp (fn, [arg]))
	| SystemF.EIf (cond, then_branch, else_branch) ->
    let cond' = tr_expr env cond in
    let then_branch' = tr_expr env then_branch in
    let else_branch' = tr_expr env else_branch in
    make (EIf (cond', then_branch', else_branch'))
	| SystemF.ESeq (e1, e2) ->
    let e1' = tr_expr env e1 in
    let e2' = tr_expr env e2 in
    make (ESeq (e1', e2'))
	| SystemF.EType (alias, _, ctor_defs, body) ->
    let env = Env.add_ctors env
      (List.to_seq ctor_defs |> Seq.unzip |> fst) alias in
    tr_expr env body
	| SystemF.ECtor (ctor_name, body) ->
    let ctor_name', _ = Env.lookup_ctor env ctor_name in
    let body' = tr_expr env body in
    make (ECtor (ctor_name', body'))
	| SystemF.EMatch (sub_expr, clauses, tp) ->
    let sub_expr' = tr_expr env sub_expr in
    let clauses' = tr_clauses env tp clauses in
    make (EMatch (sub_expr', clauses'))

and tr_clauses env tp = function
  | [] when tp = SystemF.TEmpty -> []
  | [] -> failwith "internal error"
  | clauses ->
    let f (ctor_name, x, body) =
      let ctor_name', _ = Env.lookup_ctor env ctor_name in
      let body' = tr_expr env body in
      (ctor_name', x, body')
    in
    List.map f clauses

let tr_program env p =
  let env = Env.of_varname_tbl env in
  tr_expr env p

let erase_type (p, env) =
  tr_program env p
