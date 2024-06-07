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

type program = expr

(* val check_well_scoped : Env.t -> tp -> tp *)
(* val split_arrow : tp list -> tp -> tp *)
(* val infer_type : Env.t -> program -> tp *)
(* val check_type : Env.t -> program -> tp -> unit *)
val ensure_well_typed : program -> unit

val type_equal : tp -> tp -> bool

module TVarMap  : Map.S with type key = TVar.t
module TVarSet  : Set.S with type elt = TVar.t

module Coerse : sig
  val is_id     : coersion -> bool
  val unwrap_id : coersion -> tp option
  val rebuild   : coersion -> tp * tp
end



(* module Subst : sig *)
(*   val subst : tp TVarMap.t -> tp -> tp *)
(*   val subst_type : tp -> tvar -> tp -> tp *)
(*   val subst_list : tp -> tvar list -> tp list -> tp *)
(*   val subst_mapping : tp -> (tvar * tp) list -> tp *)
(*   val get_subst : TVarSet.t -> tp -> tp -> (tvar * tp) list *)
(* end *)

(* module Env : *)
(* sig *)
(*   type t = Env.t *)
(**)
(*   val empty : t *)
(*   val add_var : t -> var -> tp -> t *)
(*   val add_tvar : t -> tvar -> t * tvar *)
(*   val add_ctor : t -> var -> tp -> var -> tvar list -> t *)
(*   val extend_tvar : t -> tvar list -> t * tvar list *)
(**)
(*   val extend_ctors : *)
(*     t -> (var * tp) list -> var -> tvar list -> t *)
(**)
(*   val extend_var : t -> (var * tp) list -> t *)
(*   val lookup_var : t -> var -> tp *)
(*   val lookup_tvar : t -> tvar -> tvar *)
(*   val lookup_ctor : t -> var -> tp * var * tvar list *)
(*   val tvar_set : t -> TVarSet.t *)
(* end *)
