open Core
open Imast

include TypeInference

module TVar = Type.TVar
module TVarSet = Type.TVarSet
module TVarMap = Type.TVarMap

module Type = Type

module Schema = struct
  include Schema
  let instantiate ?mapping lvl typ =
    instantiate ?mapping lvl typ |> fst
end

module PrettyPrinter = PrettyPrinter
module Level = Type.Level

