open Main
open Core.Imast

type ('a, 'c) ctx

val pp_context : unit -> (tvar, var) ctx

val pp_lookup_tvar : ?ctx:(tvar, var) ctx -> tvar -> string
val pp_lookup_var  : ?ctx:(tvar, var) ctx -> var -> string

val pp_type : ?ctx:(tvar, var) ctx -> Main.tp -> string

val pp_expr : ?ctx:(tvar, var) ctx -> Utils2.Env.t -> Main.expr -> string

val pp_ctx : unit -> string
