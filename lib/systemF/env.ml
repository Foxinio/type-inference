(** Typing environments *)

open Type
open Core

type t =
  { var_map   : tp VarMap.t;
    tvar_map  : tvar TVarMap.t;
    ctor_map  : (tp*name*tvar list) VarMap.t;
    eff_stack : Effect.uvar list;
  }

let empty =
  { var_map   = VarMap.empty;
    tvar_map  = TVarMap.empty;
    ctor_map  = VarMap.empty;
    eff_stack = [];
  }

let add_var env x tp =
  { env with var_map = VarMap.add x tp env.var_map }

let add_tvar env a =
  let b = TVar.fresh () in
  { env with tvar_map = TVarMap.add a b env.tvar_map}, b

let add_ctor env ctor_name expected adt_name adt_args =
  { env with ctor_map = VarMap.add ctor_name (expected, adt_name, adt_args) env.ctor_map }


let extend_var env lst =
  let f env (name,tp) = add_var env name tp in
  List.fold_left f env lst

let extend_tvar env lst =
  let f (env,lst) x =
    let env, y = add_tvar env x in
    env, y :: lst
  in
  List.fold_left f (env, []) lst

let extend_ctors env lst name tvars =
  let f env (name,tp) = add_ctor env name tp name tvars in
  List.fold_left f env lst


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

let push_eff_stack env =
  { env with eff_stack = Effect.fresh_uvar () :: env.eff_stack }

let pop_eff_stack env = List.hd env.eff_stack

let impure_top env = List.hd env.eff_stack |> Effect.get_val

let tvar_set env =
  TVarMap.to_seq env.tvar_map |> Seq.map fst |> TVarSet.of_seq
