(* LICENSE *)

type t =
  | EffPure
  | EffImpure

let compare a b =
  match a, b with
  | EffPure, EffPure -> 0
  | EffPure, EffImpure -> -1
  | EffImpure, EffPure -> 1
  | EffImpure, EffImpure -> 0

let join a b =
  match a, b with
  | EffPure, EffPure -> EffPure
  | EffImpure, _
  | _, EffImpure -> EffImpure

let pure = EffPure
let not_pure = EffImpure

let to_string = function
  | EffPure -> "pure"
  | EffImpure -> "impure"
