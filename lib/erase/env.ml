open Ast
open Core

module VarTbl = Imast.VarTbl
module VarMap = Imast.VarMap

type t = {
  name_map   : string VarTbl.t;
  ctors      : (int * SystemF.adtvar) VarMap.t;
  adt_index  : int VarMap.t;
  var_tp_map : SystemF.tp VarMap.t;
  ctor_count : int VarMap.t;
}

(* ------------------------------------------------------------------------- *)

let empty = {
  name_map   = VarTbl.create 11;
  adt_index  = VarMap.empty;
  ctors      = VarMap.empty;
  var_tp_map = VarMap.empty;
  ctor_count = VarMap.empty;
}

let with_name_map name_map = {
  ctors      = VarMap.empty;
  adt_index  = VarMap.empty;
  var_tp_map = VarMap.empty;
  ctor_count = VarMap.empty;
  name_map;
}

(* ------------------------------------------------------------------------- *)

let lookup_var env x =
  VarMap.find x env.var_tp_map

let lookup_ctor env sysF_ctor : int * SystemF.adtvar =
  VarMap.find sysF_ctor env.ctors

let lookup_var_name env x =
  VarTbl.find env.name_map x

(* ------------------------------------------------------------------------- *)

let add_var env x tp =
  { env with var_tp_map=VarMap.add x tp env.var_tp_map }

(* ------------------------------------------------------------------------- *)

let rec extend_vars env xs tp =
  match xs, tp with
  | x :: xs, SystemF.TArrow(_, tp1, tp2) ->
    extend_vars (add_var env x tp1) xs tp2
  | [], _ -> env
  | _, _ -> failwith "internal type error"

let extend_ctors env keys tp =
  let values = Seq.zip (Seq.ints 0) (Seq.repeat tp) in
  let ctors_seq = Seq.zip keys values in
  let ctors = VarMap.add_seq ctors_seq env.ctors in
  let max = Seq.fold_left (fun _ (_, (i,_)) -> i) 0 ctors_seq in
  let ctor_count = VarMap.add tp max env.ctor_count in
  { env with ctors; ctor_count }

(* ------------------------------------------------------------------------- *)

let get_ctx env =
  VarTbl.to_seq env.name_map |> SystemF.PrettyPrinter.pp_context_of_seq

