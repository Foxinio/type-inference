open Core
open Imast


type program = Type.t Imast.expr * string Imast.VarTbl.t

val infer : Imast.program -> program

module TVar : Tvar.TVar_S
module TVarSet : Set.S with type elt = TVar.t
module TVarMap : Map.S with type key = TVar.t

module Level : sig
  type t
  val starting : t
  val increase : t -> t
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

end

module Type : sig
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

  val view  : t -> view

  val t_unit   : t
  val t_empty  : t
  val t_bool   : t
  val t_int    : t
  val t_var    : TVar.t -> t
  val t_arrow  : t list -> t -> t
  val t_adt    : IMAstVar.t -> Level.t -> t list -> t
  val t_pair   : t -> t -> t
  val t_prod   : t list -> t

  exception Cannot_compare of t * t

  module UVarSet : Set.S with type elt = uvar

  val fresh_uvar : Level.t -> t
  val fresh_gvar : Level.t -> t
  val fresh_tvar : unit -> t
  val set_uvar : uvar -> t -> unit
  val uvar_compare : uvar -> uvar -> int

end


