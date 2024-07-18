(* LICENSE *)

open Core.Effect
open Folding

type uvar = (eff_uvar_state * fold_uvar_state) ref
and eff_uvar_state =
  | Impure

  (* holds list of uvars determined to be greater or equal to this.
   * meaning if this uvar is determined to be impure, 
   * every uvar on the list shoud be too
   *)
  | EUnknown of uvar list
and fold_uvar_state =
  | Unfolded
  | FUnknown of uvar list

let fresh () : uvar = ref (EUnknown [], FUnknown [])

let view_eff (x : uvar) =
  match !x with
  | EUnknown _,_ -> EffPure
  | Impure, _   -> EffImpure

let view_fold (x : uvar) =
  match !x with
  | _, FUnknown _ -> FldFolded
  | _, Unfolded  -> FldUnfolded

let view x = view_eff x, view_fold x

let set_unfolded (x : uvar) =
  x := fst !x, Unfolded

let set_impure (x : uvar) =
  x := Impure, snd !x

let link_fold (x : uvar) y =
  match !x with
  | eff, FUnknown lst ->
    x := eff, FUnknown (y :: lst)
  | _ -> failwith "internal error"

let link_eff (x : uvar) y =
  match !x with
  | EUnknown lst, fold ->
    x := EUnknown (y :: lst), fold
  | _ -> failwith "internal error"

let unify_uvar (x : uvar) y =
  (match fst !x with
  | EUnknown lst ->
    link_eff x y
  | Impure ->
    set_impure y);
  match snd !y with
  | FUnknown lst ->
    link_fold y x
  | Unfolded ->
    set_unfolded x

let is_impure x = view_eff x = EffImpure
let is_unfolded x = view_fold x = FldUnfolded


(* Order on modifiers *)

let subtype x y =
  match x, y with
  | x, y when x = y -> true
  | (EffPure, _), _
  | (_, FldUnfolded), _ -> true
  | (EffImpure, _), (EffPure, _) -> false
  | (EffImpure, FldFolded), (_, _) -> false

let equal x y = subtype x y && subtype y x

let subtype_uvar x y =
  subtype (view x) (view y)

let equal_uvar x y =
  equal (view x) (view y)

(* let rec compare x y = *)
(*   match view x, view y with *)
(*   | x, y when x = y -> 0 *)
(*   | (EffPure, _), (EffPure, _) -> 0 *)
(*   | (EffPure, _), (EffImpure, _) -> -1 *)
(*   | (EffImpure, FldUnfolded), (EffImpure, FldFolded) -> -1 *)
(*   | _ -> - compare y x *)
