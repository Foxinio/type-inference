
include FillEffects
include FillFolding

let pp_program p = PrettyPrinter.pp_expr Utils2.Env.empty p

include Main
include Order
include EnsureWellTyped

include Subst
module Env   = Env
module PrettyPrinter = struct
  include PrettyPrinter

  let pp_expr ?(ctx=pp_context()) env e = pp_expr ~ctx (Env.to_env2 env) e
end
module Folding = Folding
module Arrow = Arrow

