(** Typing environments *)

open Core
open Imast
open Main

type t =
  { var_map  : tp VarMap.t;
    tvar_map : tvar TVarMap.t;
    ctor_map : (tp*name*tvar list) VarMap.t;
  }

(* ------------------------------------------------------------------------- *)

let empty =
  { var_map  = VarMap.empty;
    tvar_map = TVarMap.empty;
    ctor_map = VarMap.empty;
  }

(* ------------------------------------------------------------------------- *)

let add_var env x tp =
  { env with var_map = VarMap.add x tp env.var_map }

let add_tvar env a =
  let b = TVar.fresh () in
  { env with tvar_map = TVarMap.add a b env.tvar_map}, b

let add_ctor env (ctor_name, expected) adt_name adt_args =
  { env with ctor_map = VarMap.add ctor_name (expected, adt_name, adt_args) env.ctor_map }

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
  let f (env,lst) x =
    let env, y = add_tvar env x in
    env, y :: lst
  in
  List.fold_left f (env, []) lst

let extend_ctors env lst alias_name tvars =
  let f env ctor = add_ctor env ctor alias_name tvars in
  List.fold_left f env lst

(* ------------------------------------------------------------------------- *)

let lookup_var env x =
  match VarMap.find_opt x env.var_map with
  | None -> failwith "Internal error: unbound variable"
  | Some tp -> tp

let lookup_tvar env x =
  match TVarMap.find_opt x env.tvar_map with
  | None -> failwith "Internal error: unbound type variable"
  | Some x -> x

let lookup_ctor env x =
  match VarMap.find_opt x env.ctor_map with
  | None -> failwith "Internal error: unbound constructor"
  | Some tp -> tp

let tvar_set env =
  TVarMap.to_seq env.tvar_map
    |> Seq.map fst
    |> TVarSet.of_seq

(* ------------------------------------------------------------------------- *)

let fresh_var () =
  let name = VarTbl.gen_name () in
  let x = Core.Imast.VarTbl.fresh_var name in
  x

let pp_vars {var_map; _} =
  VarMap.to_seq var_map
    |> Seq.map (fun (x,tp) -> Printf.sprintf "(%s : %s)"
      (Core.Imast.VarTbl.find x) (PrettyPrinter.pp_type tp))
    |> List.of_seq
    |> String.concat ", "
    |> Printf.sprintf "[%s]"
