
let transform_with_effects = FillEffects.transform_with_effects
let transform_with_folding = FillFolding.transform_with_folding

let pp_program (p,env) =
  let ctx = Env.with_name_map env |> Env.get_ctx in
  PrettyPrinter.pp_expr ctx p

include Main
include Order
include EnsureWellTyped

module Subst = Subst
module Env   = Env
module PrettyPrinter = PrettyPrinter
module Folding = Folding
module Arrow = Arrow

