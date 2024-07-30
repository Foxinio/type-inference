open Core

exception Out_of_scope of string * Ast.expl_type Ast.expr
