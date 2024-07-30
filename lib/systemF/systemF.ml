
let transform_with_effects = FillEffects.transform_with_effects
let transform_with_folding = FillFolding.transform_with_folding

let pp_program = PrettyPrinter.pp_expr

include Main
include Order
include EnsureWellTyped

module Subst = Subst
module Env   = Env
module PrettyPrinter = PrettyPrinter
module Folding = Folding
module Arrow = Arrow

