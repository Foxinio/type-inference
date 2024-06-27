(* LICENSE *)

type t =
  | Unknown
  | Pure
  | Impure

type uvar = t ref

let set_uvar x eff =
  x := eff

let impure_uvar x =
  x := Impure

let get_val x = !x

let fresh_uvar () = ref Pure

let compare a b =
  match a, b with
  | a, b when a = b -> 0
  | Unknown, Pure -> 1
  | _, Impure -> 1
  | a, b -> - compare b a

let join a b =
  match a, b with
  | Unknown, eff
  | eff, Unknown -> eff
  | Pure, Pure -> Pure
  | Impure, _
  | _, Impure -> Impure

let join_uvar a b =
  let joined = join !a !b in
  a := joined;
  b := joined

let pure = Pure
let not_pure = Impure
let unknown = Unknown

let equal_mod_known a b =
  match a,b with
  | _ when a = b -> true
  | Unknown, _ | _, Unknown -> true
  | _ -> false
