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

  (* Same as above, but instead holds list of lesser uvars,
   * and so once determined to be unfolded,
   * will determin every uvar on the list
   *)
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

(* ASK if this is what was expected *)
let rec set_unfolded (x : uvar) =
  match !x with
  | Impure, FUnknown lst ->
    x := fst !x, Unfolded;
    List.iter set_unfolded lst

  (* in this case if uvar is determined to be pure,
     unfolding information isn't propagated,
     lets see how it does *)
  | EUnknown _, FUnknown _ ->
    x := fst !x, Unfolded
  | _, Unfolded -> ()

let rec set_impure (x : uvar) =
  match fst !x with
  | EUnknown lst ->
    x := Impure, snd !x;
    List.iter set_impure lst
  | Impure -> ()

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

let unify_effect (x : uvar) y =
  match fst !x with
  | EUnknown lst ->
    link_eff x y
  | Impure ->
    set_impure y

let unify_fold (x : uvar) y =
  match snd !y with
  | FUnknown lst ->
    link_fold y x
  | Unfolded ->
    set_unfolded x

let unify_uvar x y =
  unify_effect x y;
  unify_fold x y

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

