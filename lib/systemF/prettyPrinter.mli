open Core.Imast

type ('a, 'c) ctx

val pp_context : unit -> ('a, 'c) ctx
val pp_context_of_seq : ('a * string) Seq.t -> ('c, 'a) ctx

val pp_type : (Main.TVar.t, var_type) ctx -> Main.tp -> string
val string_of_type : Main.tp -> string

val pp_expr : (Main.TVar.t, var_type) ctx -> Main.expr -> string
