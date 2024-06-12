module IMAstVar = Tvar.Make()
module VarTbl = IMAstVar.MakeHashtbl()

include Ast.Make(struct
  type t = IMAstVar.t
end)

module VarMap = IMAstVar.MakeMap()
module VarSet = IMAstVar.MakeSet()

type program = expl_type expr * string VarTbl.t

