open Core
open Imast

include TypeInference

module TVar = Type.TVar
module TVarSet = Type.TVarSet
module TVarMap = Type.TVarMap

module Schema = Schema
module Effect = Type.Effect

module Type = Type
module PrettyPrint = PrettyPrinter
module Level = Type.Level

