open Core

type t

(** this is gonna be removed but is kept for now to make it compile *)
val empty : t
val of_var_names : string Imast.VarTbl.t -> t

val extend_gamma : t -> Type.t Imast.var -> Type.typ -> t
val lookup_gamma : t -> Imast.var_type -> Type.typ option

val extend_by_ctors : t -> Type.t Imast.ctor_def list -> Imast.scheme -> t
val lookup_ctor     : t -> Imast.ctor_name -> (Type.t * Imast.scheme) option

val extend_delta : t -> Imast.var_type -> Type.t -> t
val lookup_delta : t -> Imast.var_type -> Type.t option

val get_uvars : t -> Type.UVarSet.t

val extend_var_name : t -> Imast.var_type -> string -> unit
val lookup_var_name : t -> Imast.var_type -> string option
val seq_of_var_name : t -> (Imast.var_type * string) Seq.t
