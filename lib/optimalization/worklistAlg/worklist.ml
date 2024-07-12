
module ConstrVar = Core.Var.Make()

module type CONSTRAINT =
sig
  module Elem : Set.OrderedType
  module Set : Set.S with type elt = Elem.t

  type 'a t

  val makeNorm : lhs:('a -> Set.t) -> rhs:('a -> Set.t) -> 'a t
  val makeCond : t:Elem.t -> rhs':('a -> Set.t) ->
      lhs:('a -> Set.t) -> rhs:('a -> Set.t) -> 'a t

  val compare : 'a t -> 'a t -> int
  val satisfies : 'a -> 'a t -> bool
end

module Constraint(E : Set.OrderedType)
: CONSTRAINT
= struct
  module Elem = E
  module Set = Set.Make(E)
  module Id = ConstrVar
  type 'a t = 
  | Constr of {
      lhs : 'a -> Set.t;
      rhs : 'a -> Set.t;
      id : Id.t
    }
  | Cond of {
      t : Set.t;
      rhs' : 'a -> Set.t;
      lhs : 'a -> Set.t;
      rhs : 'a -> Set.t;
      id : Id.t
    }

  let get_id = function
    | Constr {id;_} -> id
    | Cond {id;_} -> id

  let makeNorm ~lhs ~rhs = Constr {lhs; rhs; id = Id.fresh ()}
  let makeCond ~t ~rhs' ~lhs ~rhs = Cond {t=Set.singleton t; rhs'; lhs; rhs; id = Id.fresh ()}

  let compare a b = Id.compare (get_id a) (get_id b)

  let satisfies x = function
    | Constr {lhs; rhs; _} ->
      Set.subset (lhs x) (rhs x)
    | Cond {t; rhs'; lhs; rhs; _} ->
      if Set.subset t (rhs' x)
      then Set.subset (lhs x) (rhs x)
      else true
end

module type ANALYSIS =
sig
  module C : CONSTRAINT
  
  
