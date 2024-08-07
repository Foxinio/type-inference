open Core.Imast
open SystemF
open Ast

type t

val empty : t

val lookup_var : t -> var -> tp
val lookup_ctor : t -> var -> int * var
val lookup_clause_count : t -> var -> int

val add_var : t -> var -> tp -> t

val extend_vars : t -> var list -> tp -> t
val extend_clause : t -> var -> var -> tp list -> t
val extend_ctors : t -> (var * tp) list -> tvar list -> var -> t

