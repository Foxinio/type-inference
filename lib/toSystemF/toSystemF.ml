module Coerse = SystemF.Coerse
open Typing
open Core

let extract_eff (e : Schema.typ Imast.expr) = 
  match Schema.get_template e.typ |> Type.view with
  | Type.TArrow(eff, _, _) -> eff
  | _ -> raise (Invalid_argument "cannot extract from non-arrow")

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
  | TArrow(eff, tps, tp) ->
    SystemF.TArrow(eff, List.map (tr_type env) tps, tr_type env tp)
  | TPair(tp1, tp2) ->
    SystemF.TPair(tr_type env tp1, tr_type env tp2)
  | TADT(a, _, tps) ->
    SystemF.TADT(a, List.map (tr_type env) tps)

let tr_var env (name,tp) =
  name, tr_type env @@ Schema.get_template tp

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

  | Imast.EExtern (name, tp, arg1) ->
    let tp' = tr_type env @@ Schema.get_template tp in
    let arg1' = tr_type env @@ Schema.get_template arg1 in
    SystemF.EExtern (name, tp', arg1')

  | Imast.EFn(xs, body) ->
    let lst = List.map (tr_var env) xs in
    SystemF.EFn(lst, tr_expr env body, extract_eff e)

  | Imast.EFix(f, xs, body) ->
    let f, _ = tr_var env f in
    let lst = List.map (tr_var env) xs in
    let tpres = tr_type env @@ Schema.get_template body.typ in
    SystemF.EFix(f, lst, tpres, tr_expr env e, extract_eff e)

  | Imast.EApp(e1, es) ->
    let rec inner e1 es tp = 
      begin match Type.view tp with
      | Type.TArrow (eff, tps, tpres) ->
        let es, es' = Utils.split_list es (List.length tps) in
        let es = List.map2 (add_coersion env) es tps in
        let e1' = SystemF.EApp (e1, es) in
        inner e1' es' tpres
      | _ -> failwith "internal error"
      end in
    inner (tr_expr env e1) es @@ Schema.get_template e1.typ

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

  | Imast.ETypeAlias (alias, typ, rest) ->
    (* at this point this expr doesn't do anything *)
    tr_expr env rest

  | Imast.EMatch (sub_expr, clauses) ->
    let tp = Schema.get_template e.typ |> tr_type env in
    let f (ctor,(x,_),e) = ctor, x, tr_expr env e in
    let clauses' = List.map f clauses in
    SystemF.EMatch(tr_expr env sub_expr, clauses', tp)

  and add_coersion env (e1 : Schema.typ Imast.expr) tp =
    let coerse = build_coersion env (Schema.get_template e1.typ) tp in
    match Coerse.is_id coerse with
    | true -> tr_expr env e1
    | false -> SystemF.ECoerse (coerse, tr_expr env e1)

  and build_coersion env tp_from tp_to =
      let opt_cons = function
        | None, _  | _, None -> None
        | Some lst, Some tp -> Some (tp :: lst) in
      let fold_coers known =
        let rec inner (acc1, acc2) tps1 tps2 =
          match tps1, tps2 with
          | tp1 :: tps1, tp2 :: tps2 ->
            let c = build_coersion env tp1 tp2 in
            inner (opt_cons (acc1, Coerse.unwrap_id c), c :: acc2) tps1 tps2
          | [], [] ->
            begin match acc1 with
            | Some acc1 -> Either.Left (List.rev acc1)
            | None -> Either.Right (List.rev acc2)
            end
          | _ -> failwith "internal error" in
          let acc = if known then Some [] else None in
          inner (acc, [])
      in
    match Type.view tp_from, Type.view tp_to with
    | (Type.TGVar (_, _) | Type.TUVar _), _ ->
      failwith "Unification variable unrealized"

    | Type.TUnit, Type.TUnit
    | Type.TBool, Type.TBool
    | Type.TInt, Type.TInt -> SystemF.CId (tr_type env tp_to)

    | Type.TVar x, Type.TVar y when TVar.compare x y = 0 ->
      SystemF.CId (tr_type env tp_from)

    | Type.TEmpty, _ ->
      SystemF.CBot (tr_type env tp_from)

    | Type.TADT (name_from, _, args_from),
      Type.TADT (name_to, _, args_to)
        when name_from = name_to ->
      assert (List.for_all2 Type.equal args_from args_to);
      SystemF.CId (tr_type env tp_to)

    | Type.TArrow (eff_from, tps_from, tpres_from), Type.TArrow (eff_to, tps_to, tpres_to) ->
      let len_from, len_to = List.length tps_from, List.length tps_to in
      if len_from = len_to then
        let coerse_res = build_coersion env tpres_from tpres_to in
        match fold_coers (Coerse.is_id coerse_res) tps_to tps_from with
        | Either.Left tps ->
          SystemF.CId (SystemF.TArrow (tps, Coerse.unwrap_id coerse_res |> Option.get))
        | Either.Right coers ->
          SystemF.CArrow (coers, coerse_res)
      (* TODO: Reverse direction of inequation *)
      (* ~this should be correct right now *)
      else if len_from < len_to then
        let tps_to, tps_to' = Utils.split_list tps_to len_from in
        let coers = fold_coers false tps_to tps_from
          |> Either.fold
            ~left:(List.map (fun tp -> SystemF.CId tp))
            ~right:Fun.id
        in
        SystemF.CSubArrow (coers,
          build_coersion env tpres_from
          (Type.t_arrow tps_to' tpres_to))
      else
        failwith "internal error"

    | Type.TPair (tp1_from, tp2_from), Type.TPair (tp1_to, tp2_to) ->
      let coers1 = build_coersion env tp1_from tp1_to in
      let coers2 = build_coersion env tp2_from tp2_to in
      begin match coers1, coers2 with
        | SystemF.CId tp1, SystemF.CId tp2 ->
          SystemF.CId (SystemF.TPair (tp1, tp2))
        | _ ->
          SystemF.CPair (coers1, coers2)
      end

    | (Type.TUnit | Type.TBool | Type.TInt | Type.TVar _| Type.TADT _ | Type.TArrow _ | Type.TPair _), _ ->
      failwith "internal error"


let tr_program ((p,env) : program) : SystemF.program =
  tr_expr Env.empty p, env

