(* Ast data definitions and helper functions *)

open Core

exception RuntimeError of string

type ('a,'extra) node = {
  data : 'a;
  extra : 'extra;
}

let make data = { data; extra=() }

type var       = Imast.IMAstVar.t
type ctor_name = int

type 'extra value =
  | VUnit
  | VInt  of int
  | VBool of bool
  | VPair of 'extra value * 'extra value
  | VADT  of var * 'extra value 
  | VClo  of ('extra value -> 'extra value)

and 'extra expr = ('extra expr_data, 'extra) node
and 'extra expr_data =
  | EUnit
  | EBool   of bool
  | ENum    of int
  | EVar    of var
  | EExtern of ('extra value -> 'extra value)
  | EFn     of var list * 'extra expr
  | EFix    of var * var list * 'extra expr
  | EApp    of 'extra expr * 'extra expr list
  | ELet    of var * 'extra expr * 'extra expr
  | EPair   of 'extra expr * 'extra expr
  | EIf     of 'extra expr * 'extra expr * 'extra expr
  | ESeq    of 'extra expr * 'extra expr
  (* | EType   of var * var list * 'extra expr *)
  | ECtor   of ctor_name * 'extra expr
  | EMatch  of 'extra expr * 'extra clause list

and 'extra clause = ctor_name * var * 'extra expr



type 'a program = 'a expr

let unimplemented () = failwith "unimplemented"
