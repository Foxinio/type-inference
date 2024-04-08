open Core

type program = Type.typ Imast.expr * string Imast.VarTbl.t

val infer : Imast.program -> program
