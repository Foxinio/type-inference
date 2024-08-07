open Core
open Imast


module TVar : Var.VAR
module TVarSet : Set.S with type elt = TVar.t
module TVarMap : Map.S with type key = TVar.t

module Level : module type of Type.Level

module Schema : sig
  type t
  type typ

  val typ_mono : t -> typ
  val typ_schema : TVarSet.t -> t -> typ

  val instantiate : ?mapping:t TVarMap.t -> Level.t -> typ -> t
  val generalize : Level.t -> t -> typ

  val get_arguments : typ -> TVarSet.t
  val get_template : typ -> t
end

type program = Schema.typ Imast.expr

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
    | TUVar   of uvar
    | TArrow  of t * t
    | TPair   of t * t

  val view  : t -> view

  val t_unit   : t
  val t_empty  : t
  val t_bool   : t
  val t_int    : t
  val t_var    : TVar.t -> t
  val t_arrow  : t -> t -> t
  val t_adt    : IMAstVar.t -> Level.t -> t list -> t
  val t_pair   : t -> t -> t

  val equal : t -> t -> bool

  exception Cannot_compare of t * t
  exception Level_difference of IMAstVar.t * Level.t * Level.t

  module UVarSet : Set.S with type elt = uvar

  val fresh_uvar : Level.t -> t
  val fresh_tvar : unit -> t
  val set_uvar : uvar -> t -> unit
  val uvar_compare : uvar -> uvar -> int

end

module PrettyPrinter : sig
  type ('a, 'b, 'c) ctx

  val pp_context : unit -> ('a, 'b, var_type) ctx

  val pp_lookup_tvar : ?ctx:(TVar.t, Type.uvar, var_type) ctx -> TVar.t -> string
  val pp_lookup_var  : ?ctx:(TVar.t, Type.uvar, var_type) ctx -> var_type -> string
  val pp_lookup_uvar : ?ctx:(TVar.t, Type.uvar, var_type) ctx -> Type.uvar -> string

  val pp_type : ?ctx:(TVar.t, Type.uvar, var_type) ctx -> Type.t -> string

  val pp_expr : ?ctx:(TVar.t, Type.uvar, var_type) ctx -> Schema.typ expr -> string

  val pp_ctx : unit -> string
end

