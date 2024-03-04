(** Abstract syntax tree of a parsed program *)

(** Node of AST, that contains additional information about the location,
  *   and optionally type if it was given by user                         *)

type ('expr, 'typ) node = {
  data      : 'expr;
  typ       : 'typ;
  start_pos : Lexing.position;
  end_pos   : Lexing.position
}

module Make(VarType : sig type t end) = struct

  type var_type = VarType.t

  type 'typ var       = var_type * 'typ
  type      ctor_name = var_type
  type 'typ ctor_def  = ctor_name * 'typ
  type      scheme    = var_type * var_type list 

  type 'typ expr = ('typ expr_data, 'typ) node
  and 'typ expr_data =
    | EUnit
    | EBool   of bool
    | ENum    of int
    | EVar    of 'typ var
    | EFn     of 'typ var list * 'typ expr
    | EFix    of 'typ var * 'typ var list * 'typ expr
    | EApp    of 'typ expr * 'typ expr list
    | ELet    of 'typ var * 'typ expr * 'typ expr
    | EPair   of 'typ expr * 'typ expr
    | EFst    of 'typ expr
    | ESnd    of 'typ expr
    | EIf     of 'typ expr * 'typ expr * 'typ expr
    | ESeq    of 'typ expr * 'typ expr
    | EAbsurd of 'typ expr
    | ETypeAlias of scheme * 'typ * 'typ expr
    | EType   of scheme * 'typ ctor_def list * 'typ expr
    (* ECtor is equivalent to EFold *)
    | ECtor   of ctor_name * 'typ expr
    (* EMatch is equivalent to EUnfold *)
    | EMatch  of 'typ expr * 'typ match_clause list

  and 'typ match_clause = ctor_name * 'typ var * 'typ expr

  type expl_type =
    | TUnit
    (* this hole means there was a gap in type given by the user *)
    | THole
    | TInt
    | TBool
    | TVar of var_type
    | TSchema of var_type * expl_type list
    | TProd of expl_type list
    | TArrow of expl_type list * expl_type

end


include Make(struct
  type t = string
end)


type program = expl_type expr
