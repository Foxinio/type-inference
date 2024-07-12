open Core

(** Unfolded means normal arrow, Folded means comma
  * we want to maximise latter
  *)
type t =
  | Folded
  | Unfolded

module FoldVar = Var.Make()

type uvar = t ref * FoldVar.t

let is_folded ((uvar,_) : uvar) =
  !uvar = Folded

let compare ((_,id1) : uvar) ((_,id2) : uvar) = FoldVar.compare id1 id2

let fresh () = (ref Unfolded, FoldVar.fresh ())

let set_uvar ((x,_) : uvar) f =
  x := f

let view (x,_) = !x

let merge (x,_) =
  x := Folded

let split (x,_) =
  x := Unfolded
