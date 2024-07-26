open Core.Imast

type t

(** this is gonna be removed but is kept for now to make it compile *)
val empty : t
val of_var_names : string VarTbl.t -> t

val extend_gamma : t -> Schema.typ var_def -> t
val lookup_gamma : t -> var_type -> Schema.typ option

val extend_by_ctors :
  t ->
  Schema.typ ctor_def list ->
  var_type ->
  Type.t list ->
  Type.TVarSet.t -> t
val lookup_ctor     : t -> var_type -> (Schema.typ * Schema.typ) option

val extend_delta_with_alias : t -> Schema.typ var_def -> t
val extend_delta_with_adt : t -> var_type -> Type.t list -> Type.TVarSet.t -> t
val extend_delta_of_list : t -> Type.t var_def list -> t
val lookup_delta : t -> var_type -> Schema.typ option

val extend_var_name : t -> var_type -> string -> unit
val lookup_var_name : ?default:string -> t -> var_type -> string
val get_ctx : t -> ('a, 'b, var_type) PrettyPrinter.ctx


val increase_level_major : t -> t
val increase_level_minor : t -> t

val string_of_level : t -> string

val fresh_uvar : t -> Type.t
val instantiate : ?mapping:Type.t Type.TVarMap.t -> t -> Schema.typ -> Type.t * Type.t list
val generalize : t -> Type.t -> Schema.typ

