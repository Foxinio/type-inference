(** Internal representation of types *)

include Main

module Level = Level
module Schema = Schema
module Effect = Effect

include Type_visitors
include Uvar
include Order
include Utils
