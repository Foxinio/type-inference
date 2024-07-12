module type VAR = sig
  type t

  val compare : t -> t -> int

  val fresh : unit -> t
  val hash : t -> int

  module MakeMap() : Map.S with type key = t
  module MakeSet() : Set.S with type elt = t
  module MakeHashtbl() : Hashtbl.S with type key = t
end

module Make() = struct
  include Int

  let next_fresh = ref 0
  let fresh () =
    let x = !next_fresh in
    next_fresh := x + 1;
    x

  let hash = Int.hash

  module MakeMap() = Map.Make(Int)
  module MakeSet() = Set.Make(Int)
  module MakeHashtbl() = Hashtbl.Make(Int)
end
