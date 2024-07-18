(* System F Type and Expr definitions *)

open Core.Imast

module TVar = Core.Var.Make()

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

type program = expr * string VarTbl.t

module VarMap  = IMAstVar.MakeMap()
module TVarMap = Map.Make(TVar)
module TVarSet = Set.Make(TVar)

let impure_arr = function
  | TArrow (arr, _, _)  -> Arrow.set_impure arr
  | _ -> assert false

let split_arr = function
  | TArrow (arr, _, _) -> Arrow.set_unfolded arr
  | _ -> assert false

