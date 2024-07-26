open Core.Imast

type ('a, 'b, 'c) ctx

val pp_context : unit -> ('a, 'b, 'c) ctx
val pp_context_of_seq : ('a * string) Seq.t -> ('b, 'c, 'a) ctx

val pp_type : (Type.TVar.t, Type.uvar, var_type) ctx -> Type.t -> string
val string_of_type : Type.t -> string

val pp_expr_with_ctx :
  (Type.TVar.t, Type.uvar, var_type) ctx -> Schema.typ expr -> string
val pp_expr_with_tbl : string VarTbl.t -> Schema.typ expr -> string

