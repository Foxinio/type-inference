module type TVar_S = sig
  type t

  val compare : t -> t -> int

  val fresh : unit -> t

  module MakeMap() : Map.S with type key = t
  module MakeSet() : Set.S with type elt = t
  module MakeHashtbl() : Hashtbl.S with type key = t
end

module Make() : TVar_S
