open Core.Imast
open SystemF



type t = {
  tvar_map : tvar Typing.TVarMap.t;
}

let empty = {
  tvar_map = Typing.TVarMap.empty;
}

let add_tvar env a =
  let b = TVar.fresh () in
  { tvar_map = Typing.TVarMap.add a b env.tvar_map}, b

let extend_tvar env =
  let f (env, lst) x =
    let env, tvar = add_tvar env x in
    env, tvar::lst
  in
 List.fold_left f (env,[])

let lookup_tvar env x =
match Typing.TVarMap.find_opt x env.tvar_map with
| None -> failwith "Internal error: unbound type variable"
| Some x -> x

