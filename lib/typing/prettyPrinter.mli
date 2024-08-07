open Core.Imast
open Type

type ('a, 'b, 'c) ctx


val pp_context : unit -> ('a, 'b, var_type) ctx

val pp_lookup_tvar : ?ctx:(TVar.t, uvar, var_type) ctx -> TVar.t -> string
val pp_lookup_var  : ?ctx:(TVar.t, uvar, var_type) ctx -> var_type -> string
val pp_lookup_uvar : ?ctx:(TVar.t, uvar, var_type) ctx -> uvar -> string

val pp_type : ?ctx:(TVar.t, uvar, var_type) ctx -> Type.t -> string

val pp_expr : ?ctx:(TVar.t, uvar, var_type) ctx -> Schema.typ expr -> string

val pp_ctx : unit -> string
