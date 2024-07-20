open Core

type uvar

val fresh : unit -> uvar

val view_eff : uvar -> Effect.t
val view_fold : uvar -> Folding.t
val view : uvar -> Effect.t * Folding.t

val set_unfolded : uvar -> unit
val set_impure : uvar -> unit
val unify_uvar : uvar -> uvar -> unit

val is_impure : uvar -> bool
val is_unfolded : uvar -> bool

val subtype :
  Effect.t * Folding.t ->
  Effect.t * Folding.t ->
  bool

val equal :
  Effect.t * Folding.t ->
  Effect.t * Folding.t ->
  bool

val subtype_uvar : uvar -> uvar -> bool
val equal_uvar : uvar -> uvar -> bool

