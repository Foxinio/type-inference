(** System F Type and Expr definitions *)

open Core
open Imast


module TVar = Tvar.Make()

let var_compare = IMAstVar.compare

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
  | TProd    of tp list

type coersion =
  | Coer of tp * tp
  | CArrow of coersion list * coersion

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
  | EType   of tp * ctor_def list * expr
  | ECtor   of name * expr
  | EMatch  of expr * tp * clause list


and ctor_def = name * tp
and alias = name * tvar list
and clause = name * var * expr

type program = expr

module VarMap  = IMAstVar.MakeMap()
module TVarMap = Map.Make(TVar)

