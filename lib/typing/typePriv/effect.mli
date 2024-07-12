type t = Core.Effect.t = EffUnknown | EffPure | EffImpure

val compare : t -> t -> int
val join : t -> t -> t
val pure : t
val not_pure : t
val unknown : t
val equal_mod_known : t -> t -> bool

module EffVar : Core.Var.VAR

type uvar

type uvar_value =
  | Const of t
  | Unknown of Level.t
  | Link of uvar

val fresh_uvar : Level.t -> uvar
val follow_link : uvar -> uvar
val view : uvar -> t
val unwrap : uvar -> uvar_value
val set_uvar : uvar -> t -> unit
val link_uvar : uvar -> uvar -> unit
val ( ! ) : uvar -> t
val compare : uvar -> uvar -> int
val wrap_uvar : Level.t -> t -> uvar
val copy_uvar : Level.t -> uvar -> uvar
val is_impure : uvar -> bool

module EffUvMap : Map.S with type key = uvar
module EffUvSet : Set.S with type elt = uvar
module EffUvTbl : Hashtbl.S with type key = uvar

