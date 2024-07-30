(* ========================================================================== *)

open Core


exception RuntimeError of string

type var       = Imast.IMAstVar.t
type ctor_name = int

type value =
  | VUnit
  | VInt  of int
  | VBool of bool
  | VPair of value * value
  | VADT  of ctor_name * value
  | VClo  of (value list -> value)

and expr =
  | EUnit
  | EBool   of bool
  | ENum    of int
  | EVar    of var
  | EExtern of (value list -> value)
  | EFn     of var list * expr
  | EFix    of var * var list * expr
  | EApp    of expr * expr list
  | ELet    of var * expr * expr
  | EPair   of expr * expr
  | EIf     of expr * expr * expr
  | ESeq    of expr * expr
  (* | EType   of var * var list * expr *)
  | ECtor   of ctor_name * expr
  | EMatch  of expr * clause array

and clause = var * expr

type program = expr

(* ========================================================================== *)

val erase_type : SystemF.program -> program
