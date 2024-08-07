open Ast
open Core.Imast

module Env = SystemF.Env

type t = {
  ctors      : (int * SystemF.adtvar) VarMap.t;
  ctor_count : int VarMap.t;
  systemF_env : Env.t;
}

(* ------------------------------------------------------------------------- *)

let empty = {
  ctors       = VarMap.empty;
  ctor_count  = VarMap.empty;
  systemF_env = Env.empty;
}

(* ------------------------------------------------------------------------- *)

let lookup_var env = Env.lookup_var env.systemF_env

let lookup_ctor env sysF_ctor : int * SystemF.adtvar =
  match VarMap.find_opt sysF_ctor env.ctors with
  | None -> failwith ("Internal error: unbound ctor "^VarTbl.find sysF_ctor)
  | Some res -> res

let lookup_clause_count env alias_name =
  VarMap.find alias_name env.ctor_count

(* ------------------------------------------------------------------------- *)

let add_var env x tp =
  { env with systemF_env = Env.add_var env.systemF_env x tp }

(* ------------------------------------------------------------------------- *)

let rec extend_vars env xs tp =
  match xs, tp with
  | x :: xs, SystemF.TArrow(_, tp1, tp2) ->
    extend_vars (add_var env x tp1) xs tp2
  | [], _ -> env
  | _, _ -> failwith "internal type error"

let extend_ctors env ctor_defs tvars alias_name =
  let keys = List.map fst ctor_defs |> List.to_seq in
  let values = Seq.zip (Seq.ints 0) (Seq.repeat alias_name) in
  let ctors_seq = Seq.zip keys values in
  let ctors = VarMap.add_seq ctors_seq env.ctors in
  let max = Seq.fold_left (fun _ (_, (i,_)) -> i) 0 ctors_seq in
  let ctor_count = VarMap.add alias_name max env.ctor_count in
  let systemF_env = Env.extend_ctors env.systemF_env ctor_defs alias_name tvars in
  { ctors; ctor_count; systemF_env }

let extend_clause env x ctor args =
  let systemF_env, _ = Env.extend_clause env.systemF_env x ctor args in
  { env with systemF_env }

