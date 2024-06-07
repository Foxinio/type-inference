open Core
open Type
open Subst
open Order

(** Checks if type is well-scoped, and refresh its type variables according to
    the environment *)
let rec check_well_scoped env tp =
  match tp with
  | TUnit | TEmpty | TBool | TInt -> tp
  | TVar a -> TVar (Env.lookup_tvar env a)
  | TArrow(tps, tpres) ->
    TArrow(List.map (check_well_scoped env) tps, check_well_scoped env tpres)
  | TForallT(a, tp) ->
    let (env, a) = Env.extend_tvar env a in
    TForallT(a, check_well_scoped env tp)
  | TPair(tp1, tp2) ->
    TPair(check_well_scoped env tp1, check_well_scoped env tp2)
  | TADT(a, tps) ->
    TADT(a, List.map (check_well_scoped env) tps)

let split_arrow tps tpres =
  let f tp acc = TArrow([tp], acc) in
  List.fold_left f tpres tps

let rec infer_type env e =
  match e with
  | EUnit   -> TUnit
  | EBool _ -> TBool
  | ENum  _ -> TInt
  | EVar  x -> Env.lookup_var env x

  | EFn(xs, body) ->
    let f env' (x, tp) =
      let tp = check_well_scoped env tp in
      Env.add_var env' x tp, tp
    in
    let env, tp1 = List.fold_left_map f env xs in
    let tp2 = infer_type env body in
    TArrow(tp1, tp2)

  | EFix(f, lst, tpres, body) ->
    let tpres = check_well_scoped env tpres in
    let lst = List.map (fun (x,tp) -> x, check_well_scoped env tp) lst in
    let f_tp = split_arrow (List.map snd lst) tpres in
    let env = Env.extend_var (Env.add_var env f f_tp) lst in
    check_type env body tpres;
    f_tp

  | EApp(e1, es) ->
    begin match infer_type env e1 with
    | TArrow(tps, tp1) when List.length tps = List.length es ->
      List.iter2 (check_type env) es tps;
      tp1
    | _ -> failwith "Internal type error"
    end

  | ETFn(a, body) ->
    let env, b = Env.extend_tvar env a in
    let tp = infer_type env body in
    TForallT(b, tp)

  | ETApp(e, tps) ->
    begin match infer_type env e with
    | TForallT(args, body) when List.length args = List.length tps ->
      let tps = List.map (check_well_scoped env) tps in
      subst_list body args tps
    | _ -> failwith "Internal type error"
    end

  | ELet(x, e1, e2) ->
    let tp1 = infer_type env e1 in
    infer_type (Env.add_var env x tp1) e2

  | EPair(e1, e2) ->
    let tp1 = infer_type env e1 in
    let tp2 = infer_type env e2 in
    TPair(tp1, tp2)

  | EFst e ->
    begin match infer_type env e with
    | TPair (tp1, _) -> tp1
    | _ -> failwith "Internal type error"
    end

  | ESnd e ->
    begin match infer_type env e with
    | TPair(_, tp2) -> tp2
    | _ -> failwith "Internal type error"
    end

  | EIf(e1, e2, e3) ->
    check_type env e1 TBool;
    let tp = infer_type env e2 in
    check_type env e3 tp;
    tp

  | ESeq(e1, e2) ->
    check_type env e1 TUnit;
    infer_type env e2

  | ECoerse(c, e) ->
    let tp_from, tp_to = Coerse.rebuild c in
    check_type env e (check_well_scoped env tp_from);
    check_well_scoped env tp_to

  | EType(alias, tvars, ctor_defs, body) ->
    let env', tvars = Env.extend_tvar env tvars in
    let env = Env.extend_ctors env ctor_defs alias tvars in
    infer_type env body

  | ECtor (name, body) ->
    let expected, alias, tvars = Env.lookup_ctor env name in
    let tp = infer_type env body in
    let adt_args = Subst.get_subst (Env.tvar_set env) expected tp |> List.map snd in
    TADT (alias, adt_args)

  | EMatch(body, defs, tp) ->
    let res_tp = check_well_scoped env tp in
    begin match infer_type env body with
    | TADT(alias, args) ->
      let f (ctor, x, e) =
        let expected, alias', tvars = Env.lookup_ctor env ctor in
        assert (Imast.IMAstVar.compare alias alias' = 0);
        let substituted = Subst.subst_list expected tvars args in
        let env = Env.add_var env x substituted in
        check_type env e res_tp in
      List.iter f defs;
      res_tp
    | TEmpty ->
      assert(List.length defs = 0);
      res_tp
    | _ -> failwith "internal error"
    end



and check_type env e tp =
  let tp' = infer_type env e in
  if type_equal tp' tp then ()
  else failwith "Internal type error"

let ensure_well_typed p =
  let _ : tp = infer_type Env.empty p in
  ()



