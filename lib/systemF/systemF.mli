open Core
open Imast


module TVar : Tvar.TVar_S

type adtvar = IMAstVar.t
type tvar = TVar.t
type var  = IMAstVar.t
type name = IMAstVar.t

type tp =
  | TUnit
  | TEmpty
  | TBool
  | TInt
  | TVar     of tvar
  | TArrow   of tp list * tp
  | TADT     of adtvar * tp list
  | TForallT of tvar list * tp
  | TPair    of tp * tp

type coersion =
  | CId       of tp
  | CBot      of tp
  | CArrow    of coersion list * coersion
  | CForallT  of tvar list * coersion
  | CPair     of coersion * coersion
  | CSubArrow of coersion list * coersion

type expr =
  | EUnit
  | EBool   of bool
  | ENum    of int
  | EVar    of var
  | ECoerse of coersion * expr
  | EFn     of (var * tp) list * expr
  | EFix    of var * (var * tp) list * tp * expr
  | EApp    of expr * expr list
  (* Big lambda: Λα.τ *)
  | ETFn    of tvar list * expr
  (* Type Application: τ* *)
  | ETApp   of expr * tp list
  | ELet    of var * expr * expr
  | EExtern of string * tp * tp
  | EPair   of expr * expr
  | EFst    of expr
  | ESnd    of expr
  | EIf     of expr * expr * expr
  | ESeq    of expr * expr
  | EType   of name * tvar list * ctor_def list * expr
  | ECtor   of name * expr
  (* tp is type of `match expr with clauses` *)
  | EMatch  of expr * clause list * tp


and ctor_def = name * tp
and alias = name * tvar list
and clause = name * var * expr

type program = expr * string Imast.VarTbl.t

val ensure_well_typed : program -> unit
val type_equal : tp -> tp -> bool

module TVarMap  : Map.S with type key = TVar.t
module TVarSet  : Set.S with type elt = TVar.t

module Coerse : sig
  val is_id     : coersion -> bool
  val unwrap_id : coersion -> tp option
  val rebuild   : coersion -> tp * tp
end

module PrettyPrinter : sig
  type ('a, 'c) ctx = ('a, 'c) PrettyPrinter.ctx

  val pp_context : unit -> ('a, 'c) ctx
  val pp_context_of_seq : ('a * string) Seq.t -> ('c, 'a) ctx

  val pp_type : (tvar, Imast.var_type) ctx -> tp -> string

  val string_of_type : tp -> string
end
