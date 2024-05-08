open Core
open Imast

module TVar : Tvar.TVar_S
module TVarSet : Set.S with type elt = TVar.t
module TVarMap : Map.S with type key = TVar.t

module Level : sig
  type t
  val starting : t
  val increase_minor : t -> t
  val increase_major : t -> t
  val compare_major : t -> t -> int
  val compare : t -> t -> int
end

type t
type uvar
type view =
  | TUnit
  | TEmpty
  | TBool
  | TInt
  | TVar    of TVar.t
  | TADT    of IMAstVar.t * Level.t * t list
  | TGVar   of uvar * view option
  | TUVar   of uvar
  | TArrow  of t list * t
  | TProd   of t list

module UVarSet : Set.S with type elt = uvar

val fresh_uvar : Level.t -> t
val fresh_gvar : Level.t -> t
val fresh_tvar : unit -> t

val t_unit   : t
val t_empty  : t
val t_bool   : t
val t_int    : t
val t_var    : TVar.t -> t
val t_arrow  : t list -> t -> t
val t_adt    : IMAstVar.t -> Level.t -> t list -> t
val t_pair   : t -> t -> t
val t_prod   : t list -> t

val view  : t -> view
val map   : ((t -> t) -> t -> t) -> t -> t
val iter  : ((t -> unit) -> t -> unit) -> t -> unit

(** The same way fold_left starts from the begining of the list and makes it way inside,
      `fold_left f init [b1; ...; bn]` is `f (... (f (f init b1) b2) ...) bn`
    foldl on trees works top-down. *)
val foldl : (('a -> t -> 'a) -> 'a -> t -> 'a) -> 'a -> t -> 'a

(** The same way fold_right starts from the end of the list and makes it way outside,
      `fold_right f [a1; ...; an] init` is `f a1 (f a2 (... (f an init) ...))`
    foldr on trees works bottom-up. Not tail-recursive. *)
val foldr : (('a -> t -> 'a) -> 'a -> t -> 'a) -> t -> 'a -> 'a

val fold_map : (('a -> t -> 'a * t) -> 'a -> t -> 'a * t) -> 'a -> t -> 'a * t

val set_uvar : uvar -> t -> unit
val uvar_compare : uvar -> uvar -> int


exception Cannot_compare of t * t

type typ

val typ_mono : t -> typ
val typ_schema : TVarSet.t -> t -> typ

val instantiate : ?mapping:t TVarMap.t -> Level.t -> typ -> t
val generalize : Level.t -> t -> typ

val get_arguments : typ -> TVarSet.t
val get_template : typ -> t
