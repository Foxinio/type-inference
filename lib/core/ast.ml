(** Abstract syntax tree of a parsed program *)

(** Node of AST, that contains additional information about the location,
  *   and optionally type if it was given by user                         *)
type ('a, 'b) node = {
  data      : 'a;
  typ       : 'b option;
  start_pos : Lexing.position;
  end_pos   : Lexing.position
}

(** Variables, field labels, and constructors are represented as strings *)
type 'a var    = string * 'a option
type ctor_name = string
type 'a scheme = string list * string * 'a

(** expressions. Each node stores additional information about the location
 * in the source, just to be able to produce better error messages. Note that
 * we do not distinguish between expressions and values: this distinction is
 * important for the semantics, but not for the programmer. Probably you will
 * need some type for representing values, but it should be defined in the
 * evaluator. *)
type 'a expr = ('a expr_data, 'a) node
and 'a expr_data =
  | EUnit
  | EBool   of bool
  | ENum    of int
  | EVar    of 'a var
  | EFn     of 'a var list * 'a expr
  | EFix    of 'a var * 'a var list * 'a expr
  | EApp    of 'a expr * 'a expr list
  | ELet    of 'a var * 'a expr * 'a expr
  | EPair   of 'a expr * 'a expr
  | EFst    of 'a expr
  | ESnd    of 'a expr
  | EInl    of 'a expr
  | EInr    of 'a expr
  | ECase   of 'a expr * 'a clause * 'a clause
  | EIf     of 'a expr * 'a expr * 'a expr
  | ESeq    of 'a expr * 'a expr
  | EAbsurd of 'a expr
  | EType   of 'a scheme * (ctor_name * 'a) list * 'a expr
  (* ECtor is equivalent to EFold *)
  | ECtor   of ctor_name * 'a expr
  (* EMatch(e, c, (x1, e1), (x2, e2)) stands
    for (match e with c x1 => e1 | x2 => e2 end) *)
  (* EMatch is equivalent to EUnfold *)
  | EMatch  of 'a expr * 'a clause list

and 'a clause = ctor_name * 'a var * 'a expr


type expl_type =
  | TUnit
  (* this hole means there was a gap in type given by the user *)
  | THole
  | TInt
  | TBool
  | TVar of string
  | TSchema of expl_type list * string
  | TProd of expl_type list
  | TCoProd of expl_type list
  | TArrow of expl_type list * expl_type


(** Complete programs. They are just 'a expressions in our case *)
type program = expl_type expr
