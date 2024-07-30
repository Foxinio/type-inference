open Core.Imast
open Typing


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

let extend_tvar env =
  let f (env, lst) x =
    let env, tvar = add_tvar env x in
    env, tvar::lst
  in
 List.fold_left f (env,[])

let lookup_tvar env x =
  match TVarMap.find_opt x env.tvar_map with
  | None -> failwith "Internal error: unbound type variable"
  | Some x -> x

let lookup_var env x =
  match VarMap.find_opt x env.var_map with
  | None -> failwith "Internal error: unbound variable"
  | Some(SystemF.TForallT(args, _) as tp) -> tp, args
  | Some tp -> tp, []
