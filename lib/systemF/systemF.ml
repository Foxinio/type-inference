
include FillEffects
include FillFolding

let pp_program = PrettyPrinter.pp_expr

include Main
include Order
include EnsureWellTyped

module Subst = Subst
module Env   = Env
module PrettyPrinter = PrettyPrinter
module Folding = Folding
module Arrow = Arrow

