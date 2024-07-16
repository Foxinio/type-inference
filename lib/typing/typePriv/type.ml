(** Internal representation of types *)

include Main

module Level = Level
module Schema = Schema

include Type_visitors
include Uvar
include Order
include Utils
