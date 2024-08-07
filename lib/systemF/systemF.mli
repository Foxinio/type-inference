open Core
open Imast

module TVar : Var.VAR

module Folding : sig
  type t =
    | FldFolded
    | FldUnfolded
end

module Arrow : sig
  type uvar

  val fresh : unit -> uvar
  val view_eff : uvar -> Effect.t
  val view_fold : uvar -> Folding.t
  val view : uvar -> Effect.t * Folding.t
  val set_unfolded : uvar -> unit
  val set_impure : uvar -> unit
  val unify_uvar : uvar -> uvar -> unit
  val is_impure : uvar -> bool
  val is_unfolded : uvar -> bool

  val subtype :
    Effect.t * Folding.t ->
    Effect.t * Folding.t ->
    bool

  val equal :
    Effect.t * Folding.t ->
    Effect.t * Folding.t ->
    bool

  val subtype_uvar : uvar -> uvar -> bool
  val equal_uvar : uvar -> uvar -> bool
end

type adtvar = IMAstVar.t
type tvar   = TVar.t
type var    = IMAstVar.t
type name   = IMAstVar.t

type tp =
  | TUnit
  | TEmpty
  | TBool
  | TInt
  | TVar     of tvar
  | TArrow   of Arrow.uvar * tp * tp
  | TADT     of adtvar * tp list
  | TForallT of tvar list * tp
  | TPair    of tp * tp

type expr =
  | EUnit
  | EBool   of bool
  | ENum    of int
  | EVar    of var
  | EFn     of var list * expr * tp
  | EFix    of var * var list * expr * tp
  | EApp    of expr * expr list
  (* Big lambda: Λα.τ *)
  | ETFn    of tvar list * expr
  (* Type Application: τ* *)
  | ETApp   of expr * tp list
  | ELet    of var * expr * expr
  | EExtern of string * tp
  | EPair   of expr * expr
  | EFst    of expr
  | ESnd    of expr
  | EIf     of expr * expr * expr
  | ESeq    of expr * expr
  | EType   of name * tvar list * ctor_def list * expr
  | ECtor   of name * tp list * expr
  (* tp is type of `match expr with clauses` *)
  | EMatch  of expr * clause list * tp

and ctor_def = name * tp
and alias = name * tvar list
and clause = name * var * expr

module TVarMap  : Map.S with type key = TVar.t
module TVarSet  : Set.S with type elt = TVar.t

module Env : sig
  type t

  val empty : t

  val add_var  : t -> var -> tp -> t
  val add_tvar : t -> tvar -> t * tvar

  val extend_tvar : t -> tvar list -> t * tvar list
  val extend_ctors : t -> (var * tp) list -> name -> tvar list -> t
  val extend_var  : t -> var list -> tp -> tp * t * Effect.t
  val extend_clause : t -> var -> var -> tp list -> t * var

  val lookup_var  : t -> var -> tp
  val lookup_tvar : t -> tvar -> tvar
  val lookup_ctor : t -> var -> tp * name * tvar list

  val to_env2 : t -> Utils2.Env.t
end

type program = expr

val infer_type : Env.t -> expr -> tp * Effect.t
val ensure_well_typed : program -> unit
val transform_with_effects : program -> program
val transform_with_folding : program -> program

val crude_transform_with_effects : program -> program
val crude_transform_with_folding : program -> program

val type_equal : tp -> tp -> bool
val subtype    : tp -> tp -> bool
val supertype  : tp -> tp -> bool

val pp_program : program -> string

val subst_type : tp -> tvar -> tp -> tp
val subst_list : tp -> tvar list -> tp list -> tp

module PrettyPrinter : sig
  type ('a, 'c) ctx

  val pp_context : unit -> (tvar, var) ctx

  val pp_lookup_tvar : ?ctx:(tvar, var) ctx -> tvar -> string
  val pp_lookup_var  : ?ctx:(tvar, var) ctx -> var -> string

  val pp_type : ?ctx:(tvar, var) ctx -> tp -> string

  val pp_expr : ?ctx:(Main.tvar, adtvar) ctx -> Env.t -> expr -> string

  val pp_ctx : unit -> string
end

