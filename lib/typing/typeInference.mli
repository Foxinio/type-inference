open Core

type program = Type.Schema.typ Imast.expr * string Imast.VarTbl.t

val infer : Imast.program -> program
