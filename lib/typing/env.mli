open Core.Imast

type t

(** this is gonna be removed but is kept for now to make it compile *)
val empty : t
val of_var_names : string VarTbl.t -> t

val extend_gamma : t -> (Schema.typ * 'a) var -> t
val lookup_gamma : t -> var_type -> Schema.typ option

val extend_by_ctors :
  t ->
  (Schema.typ * Effect.t) ctor_def list ->
  var_type ->
  Type.t list ->
  Type.TVarSet.t -> t
val lookup_ctor     : t -> var_type -> (Schema.typ * Schema.typ) option

val extend_delta_with_alias : t -> Schema.typ var -> t
val extend_delta_with_adt : t -> var_type -> Type.t list -> Type.TVarSet.t -> t
val extend_delta_of_list : t -> Type.t var list -> t
val lookup_delta : t -> var_type -> Schema.typ option

val extend_var_name : t -> var_type -> string -> unit
val lookup_var_name : ?default:string -> t -> var_type -> string
val seq_of_var_name : t -> (var_type * string) Seq.t

val increase_level_major : t -> t
val increase_level_minor : t -> t
val increase_level_eff   : t -> t

val fresh_uvar : t -> Type.t
val wrap_eff_uvar : t -> Effect.t -> Effect.uvar
val fresh_eff_uvar : t -> Effect.uvar
val instantiate : ?mapping:Type.t Type.TVarMap.t -> t -> Schema.typ -> Type.t
val generalize : t -> Type.t -> Schema.typ

(* val push_eff_uvar : t -> Effect.uvar -> t *)
(* val unpure_top_eff : t -> unit *)
(* val pop_eff_uvar : t -> Effect.uvar *)


