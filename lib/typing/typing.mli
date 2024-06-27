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

module PrettyPrint : sig
  type ('a, 'b, 'c) ctx

  val pp_context : unit -> ('a, 'b, 'c) ctx
  val pp_context_of_seq : ('a * string) Seq.t -> ('b, 'c, 'a) ctx

  val pp_type : (Type.TVar.t, Type.uvar, var_type) ctx -> Type.t -> string
  val string_of_type : Type.t -> string
end

module Schema : sig
  type t
  type typ

  val typ_mono : t -> typ
  val typ_schema : TVarSet.t -> t -> typ

  val instantiate : ?mapping:t TVarMap.t -> Type.Level.t -> typ -> t
  val generalize : Type.Level.t -> t -> typ

  val get_arguments : typ -> TVarSet.t
  val get_template : typ -> t
end

type program = Schema.typ Imast.expr * string Imast.VarTbl.t

val infer : Imast.program -> program

module Type : sig
  type t = Schema.t
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
    | TArrow  of Effect.t * t list * t
    | TPair   of t * t

  val view  : t -> view

  val t_unit   : t
  val t_empty  : t
  val t_bool   : t
  val t_int    : t
  val t_var    : TVar.t -> t
  val t_arrow  : Effect.t -> t list -> t -> t
  val t_adt    : IMAstVar.t -> Level.t -> t list -> t
  val t_pair   : t -> t -> t

  val merge : t -> t -> t
  val split : t -> t -> t
  val equal     : t -> t -> bool
  val subtype   : subtype:t -> supertype:t -> bool
  val supertype : supertype:t -> subtype:t -> bool

  exception Cannot_compare of t * t

  module UVarSet : Set.S with type elt = uvar

  val fresh_uvar : Level.t -> t
  val fresh_gvar : Level.t -> t
  val fresh_tvar : unit -> t
  val set_uvar : uvar -> t -> unit
  val uvar_compare : uvar -> uvar -> int

end


