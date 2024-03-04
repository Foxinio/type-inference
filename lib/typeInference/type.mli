open Core

module UVar : Tvar.TVar_S

type t
type uvar
type view =
  | TUnit
  | TEmpty
  | TBool
  | TInt
  | TVar    of Imast.IMAstVar.t
  | TScheme of Imast.IMAstVar.t * t list
  | TGVar   of uvar * view option
  | TUVar   of uvar
  | TArrow  of t list * t
  | TProd   of t list

module UVarSet : Set.S with type elt = uvar
module UVarMap : Map.S with type key = uvar

val fresh_uvar : unit -> t
val fresh_gvar : unit -> t

val t_unit   : t
val t_empty  : t
val t_bool   : t
val t_int    : t
val t_var    : Imast.IMAstVar.t -> t
val t_arrow  : t list -> t -> t
val t_scheme  : Imast.IMAstVar.t -> t list -> t
val t_pair   : t -> t -> t
val t_prod   : t list -> t

val view : t -> view

val set_uvar : uvar -> t -> unit
val set_gvar : uvar -> t -> unit
val t_of_uvar : uvar -> t option
val uvar_compare : uvar -> uvar -> int

exception Cannot_compare of t * t

type typ

val typ_mono : t -> typ
val typ_schema : t -> UVarSet.t -> typ

val instantiate : ?mapping:t UVarMap.t -> typ -> t
val generalize : UVarSet.t -> t -> typ

val get_uvars : typ -> UVarSet.t


