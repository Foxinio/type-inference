(** Typing environments *)

open Core
open Imast
open Main

module Tbl = IMAstVar.MakeHashtbl()

type t =
  { var_map  : tp VarMap.t;
    tvar_map : tvar TVarMap.t;
    ctor_map : (tp*name*tvar list) VarMap.t;
    constant : tp Tbl.t;
  }

(* ------------------------------------------------------------------------- *)

let empty =
  { var_map  = VarMap.empty;
    tvar_map = TVarMap.empty;
    ctor_map = VarMap.empty;
    constant = Tbl.create 11;
  }

(* ------------------------------------------------------------------------- *)

let add_tbl tbl x tp =
  match Tbl.find_opt tbl x with
  | Some tp' when Order.type_equal tp tp' -> ()
  | _ -> Tbl.add tbl x tp

let add_var env x tp =
  add_tbl env.constant x tp;
  { env with var_map = VarMap.add x tp env.var_map }

let add_tvar env a =
  let b = TVar.fresh () in
  { env with tvar_map = TVarMap.add a b env.tvar_map}, b

let add_ctor env (ctor_name, expected) adt_name adt_args =
  let ctor = expected, adt_name, adt_args in
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

let pp_vars env =
  Tbl.to_seq env.constant
    |> Seq.map (fun (x,tp) -> Printf.sprintf "(%s#%s : %s)"
      (Core.Imast.VarTbl.find x)
      (Core.Imast.IMAstVar.to_string x)
      (PrettyPrinter.pp_type tp))
    |> List.of_seq
    |> String.concat ",\n  "
    |> Printf.sprintf "[\n  %s\n]"
