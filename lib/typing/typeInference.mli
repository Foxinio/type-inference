open Core
open Type

type program = Schema.typ Imast.expr * string Imast.VarTbl.t

val infer : Imast.program -> program
