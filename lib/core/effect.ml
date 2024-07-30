(* LICENSE *)

type t =
  | EffPure
  | EffImpure

let compare a b =
  match a, b with
  | a, b when a = b -> 0
  | _, EffImpure -> 1
  | a, b -> - compare b a

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
