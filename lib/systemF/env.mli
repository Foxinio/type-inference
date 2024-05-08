(** Typing environments *)

open Type

type t

val empty : t

val add_var  : t -> var -> tp -> t
val add_tvar : t -> tvar -> t * tvar
val add_ctor : t -> var -> tp -> name -> tvar list -> t

val extend_tvar : t -> tvar list -> t * tvar list
val extend_ctors : t -> (var * tp) list -> name -> tvar list -> t
val extend_var  : t -> (var * tp) list -> t

val lookup_var  : t -> var -> tp
val lookup_tvar : t -> tvar -> tvar
val lookup_ctor : t -> var -> tp * name * tvar list

val tvar_set : t -> TVarSet.t
