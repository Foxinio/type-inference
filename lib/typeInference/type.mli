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
  | TADT    of Imast.IMAstVar.t * t list
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
val t_arrow  : t list -> t -> t
val t_adt    : Imast.IMAstVar.t -> t list -> t
val t_pair   : t -> t -> t
val t_prod   : t list -> t

val view  : t -> view
val map   : ((view -> t) -> t -> t) -> t -> t
val iter  : ((view -> unit) -> t -> unit) -> t -> unit

(** The same way fold_left starts from the begining of the list and makes it way inside,
      `fold_left f init [b1; ...; bn]` is `f (... (f (f init b1) b2) ...) bn`
    foldl on trees works top-down. *)
val foldl : (('a -> view -> 'a) -> 'a -> t -> 'a) -> 'a -> t -> 'a

(** The same way fold_right starts from the end of the list and makes it way outside,
      `fold_right f [a1; ...; an] init` is `f a1 (f a2 (... (f an init) ...))`
    foldr on trees works bottom-up. Not tail-recursive. *)
val foldr : (('a -> view -> 'a) -> 'a -> t -> 'a) -> t -> 'a -> 'a

val set_uvar : uvar -> t -> unit
val t_of_uvar : uvar -> t option
val uvar_compare : uvar -> uvar -> int
val uvar_disallow_alias : uvar -> Imast.IMAstVar.t -> unit


exception Cannot_compare of t * t

type typ

val typ_mono : t -> typ
val typ_schema : UVarSet.t -> t -> typ

val instantiate : ?mapping:t UVarMap.t -> typ -> t
val generalize : UVarSet.t -> t -> typ

val get_uvars : typ -> UVarSet.t


