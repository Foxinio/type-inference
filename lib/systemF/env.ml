(** Typing environments *)

open Core
open Imast
open Main

module Tbl = IMAstVar.MakeHashtbl()

open Utils2.Env

type t1 = 
  { tvar_map : tvar TVarMap.t;
    constant : tp Tbl.t;
  }

type t2 = t

type t = t1 * t2

(* ------------------------------------------------------------------------- *)

let empty =
  { tvar_map = TVarMap.empty;
    constant = Tbl.create 11;
  }, empty

(* ------------------------------------------------------------------------- *)

let add_tbl tbl x tp =
  match Tbl.find_opt tbl x with
  | Some tp' when Order.type_equal tp tp' -> ()
  | _ -> Tbl.add tbl x tp

let add_var (env1,env2) x tp =
  add_tbl env1.constant x tp;
  (env1, add_var env2 x tp)

let add_tvar (env1,env2) a =
  let b = TVar.fresh () in
  let env1 = { env1 with tvar_map = TVarMap.add a b env1.tvar_map} in
  (env1, add_tvar env2 a |> fst), b

let extend_var (env1,env2) xs tp =
  let rec inner env xs tp eff =
    match xs, tp with
    | x :: xs, TArrow(arr, tp1, tp2) ->
      inner (add_var env x tp1) xs tp2 (Arrow.view_eff arr)
    | _ :: _, _ ->
      failwith "internal error: expected TArrow"
    | [], tp -> ()
  in inner (env1,env2) xs tp EffPure;
  let tp, env2, eff = extend_var env2 xs tp in
  tp, (env1,env2), eff

let extend_tvar env lst =
  let f x (env,lst) =
    let env, y = add_tvar env x in
    env, y :: lst
  in
  List.fold_right f lst (env, [])

let extend_ctors (env1,env2) lst alias_name tvars =
  env1, extend_ctors env2 lst alias_name tvars

(* ------------------------------------------------------------------------- *)

let lookup_var (_,env2) x =
  lookup_var env2 x

let lookup_tvar (env1,_) x =
  match TVarMap.find_opt x env1.tvar_map with
  | None -> failwith (
    "Internal error: unbound type variable "^
    PrettyPrinter.pp_lookup_tvar x)
  | Some x -> x

let lookup_ctor (_,env2) ctor =
  lookup_ctor env2 ctor

let tvar_set (env,_) =
  TVarMap.to_seq env.tvar_map
    |> Seq.map fst
    |> TVarSet.of_seq

let extend_clause env x ctor args =
  let template, alias', tvars = lookup_ctor env ctor in
  let substituted = Subst.subst_list template tvars args in
  add_var env x substituted, alias'

(* ------------------------------------------------------------------------- *)

let pp_vars (env,_) =
  Tbl.to_seq env.constant
    |> Seq.map (fun (x,tp) -> Printf.sprintf "(%s#%s : %s)"
      (Core.Imast.VarTbl.find x)
      (Core.Imast.IMAstVar.to_string x)
      (PrettyPrinter.pp_type tp))
    |> List.of_seq
    |> String.concat ",\n  "
    |> Printf.sprintf "[\n  %s\n]"

let to_env2 ({ tvar_map;_ }, env2) : Utils2.Env.t =
  { env2 with
    tvar_set = TVarSet.of_seq (TVarMap.to_seq tvar_map |> Seq.map fst)
  }
