open Core.Imast
open Type


module TVar : Core.Var.VAR
module TVarSet : Set.S with type elt = TVar.t
module TVarMap : Map.S with type key = TVar.t

module Level : module type of Level
module Effect : module type of Effect

module PrettyPrint : sig
  type ('a, 'b, 'c) ctx

  val pp_context : unit -> ('a, 'b, 'c) ctx
  val pp_context_of_seq : ('a * string) Seq.t -> ('b, 'c, 'a) ctx

  val pp_type : (Type.TVar.t, Type.uvar, var_type) ctx -> Type.t -> string
  val string_of_type : Type.t -> string
end

module Schema : sig
  type t
  include module type of Schema
end

include module type of TypeInference

module Type : module type of Type
with type t = Schema.t


