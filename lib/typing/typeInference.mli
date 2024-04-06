open Core

type program = Type.t Imast.expr * string Imast.VarTbl.t

val infer : Imast.program -> program
