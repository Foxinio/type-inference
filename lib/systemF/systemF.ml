
let transform_with_effects = FillEffects.transform_with_effects
let transform_with_folding = FillFolding.transform_with_folding

include Type
include Order
include EnsureWellTyped

module Subst = Subst
module Env   = Env
module PrettyPrinter = PrettyPrinter
module Folding = Folding
module Arrow = Arrow

