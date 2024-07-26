module type VAR = sig
  type t

  val compare : t -> t -> int

  val fresh : unit -> t
  val hash : t -> int

  val to_string : t -> string

  module MakeMap() : Map.S with type key = t
  module MakeSet() : Set.S with type elt = t
  module MakeHashtbl() : Hashtbl.S with type key = t
end

module Make() : VAR
