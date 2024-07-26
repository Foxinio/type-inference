open Core
open Type
open Imast
open Effect

type t = {
  gamma: Schema.typ VarMap.t;
  ctors: (Schema.typ * Schema.typ) VarMap.t;
  delta: Schema.typ VarMap.t;
  var_name: string VarTbl.t;
  level: Level.t;
}

let empty = {
  gamma=VarMap.empty;
  ctors=VarMap.empty;
  delta=VarMap.empty;
  var_name=VarTbl.create 11;
  level=Level.starting;
}
let of_var_names var_name =
  { empty with var_name }


(* uvar levels *)
let increase_level_minor ({ level;_} as env) =
  { env with level=Level.increase_minor level }
let increase_level_major ({ level;_} as env) =
  { env with level=Level.increase_major level }

let string_of_level {level;_} = Level.to_string level

let fresh_uvar {level;_} = Type.fresh_uvar level

let instantiate ?(mapping=TVarMap.empty) {level;_} typ =
  Schema.instantiate ~mapping level typ

let generalize {level;_} tp =
  Schema.generalize level tp


(* Gamma *)

let extend_gamma ({gamma;_} as env) (x,tp) =
  { env with
    gamma=VarMap.add x tp gamma;
  }

let lookup_gamma {gamma; level; _} x =
  VarMap.find_opt x gamma


(* Ctors *)

let extend_by_ctors ({ctors; level;_} as env) lst alias_name alias_args set =
  let adt_t = Type.t_adt alias_name level alias_args in
  let adt_typ = Schema.typ_schema set adt_t in
  let f (var, typ) = (var, (typ, adt_typ)) in
  let seq = List.map f lst |> List.to_seq in
  { env with ctors =
      VarMap.add_seq seq ctors
  }

let lookup_ctor {ctors;_} name =
  VarMap.find_opt name ctors


(* Delta *)

let extend_delta_with_alias ({delta;_} as env) (name, typ) =
  { env with delta =
    VarMap.add name typ delta
  }

let extend_delta_with_adt ({delta; level;_} as env) name lst set =
  let adt_t = Type.t_adt name level lst in
  let adt_typ = Schema.typ_schema set adt_t in
  { env with delta =
    VarMap.add name adt_typ delta
  }

let extend_delta_of_list ({delta;_} as env) lst =
  let seq = List.map
    (fun (x,t) -> x, Schema.typ_mono t) lst
    |> List.to_seq in
  { env with delta =
    VarMap.add_seq seq delta
  }

let lookup_delta {delta;_} name = VarMap.find_opt name delta

(* var names *)

let extend_var_name {var_name;_} x name = VarTbl.add var_name x name

let lookup_var_name ?(default="<unknown>") {var_name;_} x = VarTbl.find_opt var_name x |> Option.value ~default

let get_ctx {var_name;_} =
  PrettyPrinter.pp_context_of_seq (VarTbl.to_seq var_name)
