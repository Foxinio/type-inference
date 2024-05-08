open Core

type t

(** this is gonna be removed but is kept for now to make it compile *)
val empty : t
val of_var_names : string Imast.VarTbl.t -> t

val extend_gamma : t -> Type.typ Imast.var -> t
val lookup_gamma : t -> Imast.var_type -> Type.typ option

val extend_by_ctors : t -> Type.typ Imast.ctor_def list -> Imast.var_type -> Type.t list -> Type.TVarSet.t -> t
val lookup_ctor     : t -> Imast.var_type -> (Type.typ * Type.typ) option

val extend_delta_with_alias : t -> Type.typ Imast.var -> t
val extend_delta_with_adt : t -> Imast.var_type -> Type.t list -> Type.TVarSet.t -> t
val extend_delta_of_list : t -> Type.t Imast.var list -> t
val lookup_delta : t -> Imast.var_type -> Type.typ option

val extend_var_name : t -> Imast.var_type -> string -> unit
val lookup_var_name : t -> Imast.var_type -> string option
val seq_of_var_name : t -> (Imast.var_type * string) Seq.t

val increase_level_type : t -> t
val increase_level_let : t -> t
val fresh_uvar : t -> Type.t
val fresh_gvar : t -> Type.t
val instantiate : ?mapping:Type.t Type.TVarMap.t -> t -> Type.typ -> Type.t
val generalize : t -> Type.t -> Type.typ
