(* LICENSE *)

type t =
  | EffUnknown
  | EffPure
  | EffImpure

let compare a b =
  match a, b with
  | a, b when a = b -> 0
  | EffUnknown, EffPure -> 1
  | _, EffImpure -> 1
  | a, b -> - compare b a

let join a b =
  match a, b with
  | EffUnknown, eff
  | eff, EffUnknown -> eff
  | EffPure, EffPure -> EffPure
  | EffImpure, _
  | _, EffImpure -> EffImpure

let pure = EffPure
let not_pure = EffImpure
let unknown = EffUnknown

let equal_mod_known a b =
  match a,b with
  | _ when a = b -> true
  | EffUnknown, _ | _, EffUnknown -> true
  | _ -> false
