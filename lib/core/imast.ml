module IMAstVar = Tvar.Make()
module VarTbl = IMAstVar.MakeHashtbl()

include Ast.Make(struct
  type t = IMAstVar.t
end)

type program = expl_type expr * string VarTbl.t

