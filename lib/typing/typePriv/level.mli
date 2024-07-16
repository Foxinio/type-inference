type t

val starting : t
val increase_minor : t -> t
val increase_major : t -> t
val compare_major  : t -> t -> int
val compare   : t -> t -> int
val to_string : t -> string
