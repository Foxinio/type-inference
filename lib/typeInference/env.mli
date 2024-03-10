open Core

type t

(** this is gonna be removed but is kept for now to make it compile *)
val empty : t
val of_var_names : string Imast.VarTbl.t -> t

val extend_gamma : t -> Type.t Imast.var -> Type.typ -> t
val lookup_gamma : t -> Imast.var_type -> Type.t option

val extend_by_ctors : t -> Type.typ Imast.ctor_def list -> Imast.var_type -> Type.t list -> Type.UVarSet.t -> t
val lookup_ctor     : t -> Imast.var_type -> (Type.typ * Type.UVarSet.t * Type.typ) option

val extend_delta_with_alias : t -> Type.typ Imast.var -> Type.UVarSet.t -> t
val extend_delta_with_adt : t -> Imast.var_type -> Type.t list -> Type.UVarSet.t -> t
val extend_delta_of_list : t -> Type.t Imast.var list -> t
val lookup_delta : t -> Imast.var_type -> (Type.typ * Type.UVarSet.t) option

val get_uvars : t -> Type.UVarSet.t

val extend_var_name : t -> Imast.var_type -> string -> unit
val lookup_var_name : t -> Imast.var_type -> string option
val seq_of_var_name : t -> (Imast.var_type * string) Seq.t

val increase_level : t -> t
val fresh_uvar : t -> Type.t
val fresh_gvar : t -> Type.t
val instantiate : ?mapping:Type.t Type.UVarMap.t -> t -> Type.typ -> Type.t
