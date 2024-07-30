open Core.Imast

type t

val empty : t

val lookup_var : t -> VarMap.key -> SystemF.tp
val lookup_ctor : t -> VarMap.key -> int * Ast.var

val add_var : t -> VarMap.key -> SystemF.tp -> t

val extend_vars : t -> VarMap.key list -> SystemF.tp -> t
val extend_ctors : t -> VarMap.key Seq.t -> Ast.var -> t

