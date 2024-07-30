open Ast
open Core.Imast

type t = {
  ctors      : (int * SystemF.adtvar) VarMap.t;
  adt_index  : int VarMap.t;
  var_tp_map : SystemF.tp VarMap.t;
  ctor_count : int VarMap.t;
}

(* ------------------------------------------------------------------------- *)

let empty = {
  adt_index  = VarMap.empty;
  ctors      = VarMap.empty;
  var_tp_map = VarMap.empty;
  ctor_count = VarMap.empty;
}

(* ------------------------------------------------------------------------- *)

let lookup_var env x =
  match VarMap.find_opt x env.var_tp_map with
  | None -> failwith ("Internal error: unbound variable"^VarTbl.find x)
  | Some tp -> tp

let lookup_ctor env sysF_ctor : int * SystemF.adtvar =
  match VarMap.find_opt sysF_ctor env.ctors with
  | None -> failwith ("Internal error: unbound ctor"^VarTbl.find sysF_ctor)
  | Some res -> res

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

