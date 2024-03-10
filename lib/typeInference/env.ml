open Core
open Type
open Imast

module VarMap = IMAstVar.MakeMap()

type t = {
  gamma: Type.typ VarMap.t;
  ctors: (Type.typ * Type.UVarSet.t * Type.typ) VarMap.t;
  delta: (Type.typ * UVarSet.t) VarMap.t;
  var_name: string VarTbl.t;
  level: int;
}

let empty = {
  gamma=VarMap.empty;
  ctors=VarMap.empty;
  delta=VarMap.empty;
  var_name=VarTbl.create 11;
  level=0;
}
let of_var_names var_name =
  { empty with var_name }


(* uvar levels *)
let increase_level({ level;_} as env) = { env with level=level+1 }

let fresh_uvar {level;_} = Type.fresh_uvar level
let fresh_gvar {level;_} = Type.fresh_gvar level

let instantiate ?(mapping=UVarMap.empty) {level;_} typ =
  Type.instantiate ~mapping level typ

(* Gamma *)

let extend_gamma ({ gamma;  _} as env) (x,_) tp =
  { env with
    gamma=VarMap.add x tp gamma;
  }

let lookup_gamma {gamma; level; _} x =
  VarMap.find_opt x gamma |> Option.map (Type.instantiate level)


(* Ctors *)

let extend_by_ctors ({ctors; level;_} as env) lst alias_name alias_args set =
  let adt_t = Type.t_adt alias_name level alias_args in
  let adt_typ = Type.typ_schema set adt_t in
  let f (var, typ) = (var, (typ, set, adt_typ)) in
  let seq = List.map f lst |> List.to_seq in
  { env with ctors =
      VarMap.add_seq seq ctors
  }

let lookup_ctor {ctors;_} name =
  VarMap.find_opt name ctors


(* Delta *)

let extend_delta_with_alias ({delta;_} as env) (name, typ) set =
  { env with delta =
    VarMap.add name (typ, set) delta
  }

let extend_delta_with_adt ({delta; level;_} as env) name lst set =
  let adt_t = Type.t_adt name level lst in
  let adt_typ = Type.typ_schema set adt_t in
  { env with delta =
    VarMap.add name (adt_typ, set) delta
  }

let extend_delta_of_list ({delta;_} as env) lst =
  let seq = List.map
    (fun (x,t) -> x, (Type.typ_mono t, UVarSet.empty)) lst
    |> List.to_seq in
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

