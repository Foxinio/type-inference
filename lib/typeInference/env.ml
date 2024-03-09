open Core
open Type
open Imast

module VarMap = IMAstVar.MakeMap()

type t = {
  gamma: Type.typ VarMap.t;
  ctors: (Type.typ * (Imast.var_type * Type.UVarSet.t)) VarMap.t;
  delta: (Type.typ * UVarSet.t) VarMap.t;
  var_name: string VarTbl.t
}

let empty = {
  gamma=VarMap.empty;
  ctors=VarMap.empty;
  delta=VarMap.empty;
  var_name=VarTbl.create 11
}
let of_var_names var_name =
  { empty with var_name }


(* Gamma *)

let extend_gamma ({ gamma;  _} as env) (x,_) tp =
  { env with
    gamma=VarMap.add x tp gamma;
  }

let lookup_gamma {gamma;_} x =
  VarMap.find_opt x gamma |> Option.map Type.instantiate


(* Ctors *)

let extend_by_ctors ({ctors;_} as env) lst alias =
  let f (var, typ) = (var, (typ, alias)) in
  let seq = List.map f lst |> List.to_seq in
  { env with ctors =
      VarMap.add_seq seq ctors
  }

let lookup_ctor {ctors;_} name =
  VarMap.find_opt name ctors


(* Delta *)

let extend_delta ({delta;_} as env) (name, typ) set =
  { env with delta =
    VarMap.add name (typ, set) delta
  }

let extend_delta_of_list ({delta;_} as env) lst =
  let seq = List.map (fun (x,t) -> x, (Type.typ_mono t, UVarSet.empty)) lst |> List.to_seq in
  { env with delta =
    VarMap.add_seq seq delta
  }

let lookup_delta {delta;_} name = VarMap.find_opt name delta


(* Uvars *)

let get_uvars {gamma;_} =
  VarMap.fold (fun _name typ acc ->
    Type.get_uvars typ |> UVarSet.union acc) gamma UVarSet.empty


(* var names *)

let extend_var_name {var_name;_} x name = VarTbl.add var_name x name

let lookup_var_name {var_name;_} x = VarTbl.find_opt var_name x

let seq_of_var_name {var_name;_} = VarTbl.to_seq var_name
