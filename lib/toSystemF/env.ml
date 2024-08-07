open Core.Imast
open Typing

exception Not_found_var of var_type
exception Not_found_tvar of TVar.t

type t = {
  tvar_map : SystemF.tvar TVarMap.t;
  var_map  : SystemF.tp VarMap.t;
}

let empty = {
  tvar_map = TVarMap.empty;
  var_map  = VarMap.empty;
}

let add_tvar env (a : TVar.t) =
  let b = SystemF.TVar.fresh () in
  { env with tvar_map = TVarMap.add a b env.tvar_map}, b

let add_var env (a, tp) =
  { env with var_map = VarMap.add a tp env.var_map }

let extend_tvar env lst =
  let f x (env, lst) =
    let env, tvar = add_tvar env x in
    env, tvar::lst
  in
 List.fold_right f lst (env,[])

let lookup_tvar env x =
  match TVarMap.find_opt x env.tvar_map with
  | None -> raise (Not_found_tvar x)
  | Some x -> x

let lookup_var env x =
  match VarMap.find_opt x env.var_map with
  | None -> raise (Not_found_var x)
  | Some(SystemF.TForallT(args, _) as tp) -> tp, args
  | Some tp -> tp, []
