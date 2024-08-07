open Main

module Env = struct

  type t =
    { var_map  : tp Main.VarMap.t;
      tvar_set : TVarSet.t;
      ctor_map : (tp*name*tvar list) Main.VarMap.t;
    }

(* ------------------------------------------------------------------------- *)

  let empty =
    { var_map  = VarMap.empty;
      tvar_set = TVarSet.empty;
      ctor_map = VarMap.empty;
    }

(* ------------------------------------------------------------------------- *)

  let add_tvar env x =
    { env with tvar_set = TVarSet.add x env.tvar_set }, x

  let add_var env x tp =
    { env with var_map = VarMap.add x tp env.var_map }

  let add_ctor env (ctor_name, template) adt_name adt_args =
    let ctor = template, adt_name, adt_args in
    { env with ctor_map=VarMap.add ctor_name ctor env.ctor_map }

(* ------------------------------------------------------------------------- *)

  let extend_var env xs tp =
    let rec inner env xs tp eff =
      match xs, tp with
      | x :: xs, TArrow(arr, tp1, tp2) ->
        inner (add_var env x tp1) xs tp2 (Arrow.view_eff arr)
      | _ :: _, _ ->
        failwith "internal error: expected TArrow"
      | [], tp ->
        tp, env, eff
    in inner env xs tp EffPure

  let extend_tvar env lst =
    let f x (env,lst) =
      let env, y = add_tvar env x in
      env, y :: lst
    in
    List.fold_right f lst (env, [])

  let extend_ctors env lst alias_name tvars =
    let f env ctor = add_ctor env ctor alias_name tvars in
    List.fold_left f env lst

(* ------------------------------------------------------------------------- *)

  let lookup_var env x =
    match VarMap.find_opt x env.var_map with
    | None -> failwith ("Internal error: unbound variable "^Core.Imast.VarTbl.find x)
    | Some tp -> tp

  let lookup_ctor env x =
    match VarMap.find_opt x env.ctor_map with
    | None -> failwith ("Internal error: unbound constructor "^Core.Imast.VarTbl.find x)
    | Some tp -> tp

  let tvar_set env = env.tvar_set

end


let rec infer_type env e : Main.tp * Core.Effect.t =
  match e with
  | EUnit   -> TUnit, EffPure
  | EBool _ -> TBool, EffPure
  | ENum _  -> TInt, EffPure
  | EVar x  -> Env.lookup_var env x, EffPure

  | EFn (args, body, tp) ->
    tp, EffPure

  | EFix (f, args, body, tp) ->
    tp, EffPure

  | EApp (e1, es) ->
    let tp1, eff = infer_type env e1 in
    let tres, eff = infer_app env es tp1 eff in
    tres, eff

  | ETFn(a, body) ->
    let env, b = Env.extend_tvar env a in
    let tp, eff = infer_type env body in
    TForallT(b, tp), eff

  | ETApp(e, tps) ->
    begin match infer_type env e with
    | TForallT(args, body), eff when List.length args = List.length tps ->
      Subst.subst_list body args tps, eff
    | _ -> failwith "Internal type error"
    end

  | ELet(x, e1, e2) ->
    let tp1, eff1 = infer_type env e1 in
    let tp2, eff2 = infer_type (Env.add_var env x tp1) e2 in
    tp2, Core.Effect.join eff1 eff2

  | EExtern(_, tp) ->
    tp, EffPure

  | EPair(e1, e2) ->
    let tp1, eff1 = infer_type env e1 in
    let tp2, eff2 = infer_type env e2 in
    TPair(tp1, tp2), Core.Effect.join eff1 eff2

  | EFst e ->
    begin match infer_type env e with
    | TPair (tp1, _), eff -> tp1, eff
    | _ -> failwith "Internal type error"
    end

  | ESnd e ->
    begin match infer_type env e with
    | TPair(_, tp2), eff -> tp2, eff
    | _ -> failwith "Internal type error"
    end

  | EIf(e1, e2, e3) ->
    let _, eff1 = infer_type env e1 in
    let tp, eff2 = infer_type env e2 in
    let _, eff3 = infer_type env e3 in
    tp, Core.Effect.join eff1 (Core.Effect.join eff2 eff3)

  | ESeq(e1, e2) ->
    let _, eff1 = infer_type env e1 in
    let tp, eff2 = infer_type env e2 in
    tp, Core.Effect.join eff1 eff2

  | EType(alias, tvars, ctor_defs, body) ->
    let env, tvars = Env.extend_tvar env tvars in
    let env = Env.extend_ctors env ctor_defs alias tvars in
    infer_type env body

  | ECtor (name, adt_args, body) ->
    let _, alias, _ = Env.lookup_ctor env name in
    let _, eff = infer_type env body in
    TADT (alias, adt_args), eff

  | EMatch(body, defs, tp) ->
    begin match infer_type env body with
    | TADT _, _ ->
      tp, EffImpure
    | TEmpty, eff1 ->
      assert(List.length defs = 0);
      tp, eff1
    | _ -> failwith "internal type error"
    end

  and infer_app env es tp eff =
    match es, tp with
    | [],_ -> tp, eff
    | e::es, Main.TArrow(arr, _, tp2) ->
      let _, eff' = infer_type env e in
      let eff' = Core.Effect.join eff' @@ Arrow.view_eff arr in
      infer_app env es tp2 (Core.Effect.join eff eff')
    | _ -> failwith "internal error"

let debug fmt =
  let f str =
    if true then Core.Utils.debug "%s" str
  in Printf.ksprintf f ("[SystemF]"^^fmt)

let counter = ref 0
let mark fmt =
  let f str =
    debug "[%d] %s" !counter str;
    incr counter
  in Printf.ksprintf f fmt
