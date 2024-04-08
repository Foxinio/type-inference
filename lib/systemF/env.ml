(** Typing environments *)

open Type

type t =
  { var_map  : tp VarMap.t;
    tvar_map : tvar TVarMap.t;
    ctor_map : (tp*tp) VarMap.t;
  }

let empty =
  { var_map  = VarMap.empty;
    tvar_map = TVarMap.empty;
    ctor_map = VarMap.empty;
  }

let add_var env x tp =
  { env with var_map = VarMap.add x tp env.var_map }

let add_tvar env a =
  let b = TVar.fresh () in
  { env with tvar_map = TVarMap.add a b env.tvar_map}, b

let add_ctor env ctor_name expected adt_tp =
  { env with ctor_map = VarMap.add ctor_name (adt_tp, expected) env.ctor_map }


let extend_var env lst =
  let f env (name,tp) = add_var env name tp in
  List.fold_left f env lst

let extend_tvar env lst =
  let f (env,lst) x =
    let env, y = add_tvar env x in
    env, y :: lst
  in
  List.fold_left f (env, []) lst

let extend_ctor env lst adt_t =
  let f env (name,tp) = add_ctor env name tp adt_t in
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
