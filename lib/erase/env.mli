open Core.Imast

type t

val empty : t
val with_name_map : string VarTbl.t -> t

val lookup_var : t -> VarMap.key -> SystemF.tp
val lookup_ctor : t -> VarMap.key -> int * Ast.var
val lookup_var_name : t -> VarTbl.key -> string

val add_var : t -> VarMap.key -> SystemF.tp -> t

val extend_vars : t -> VarMap.key list -> SystemF.tp -> t
val extend_ctors : t -> VarMap.key Seq.t -> Ast.var -> t

val get_ctx : t -> ('a, VarTbl.key) SystemF.PrettyPrinter.ctx

