open Imast
open Effect

(* ========================================================================== *)

let prelude_pos = { Lexing.dummy_pos with pos_fname="Prelude" }

let make data : ('a, 'b) Ast.node =
  { data; typ=Ast.THole; start_pos=prelude_pos; end_pos=prelude_pos }

module StringMap = Map.Make(String)

let builtin_functions = [
    "add",
      Ast.EExtern ("add", EffPure, Ast.t_arrow [Ast.TInt; Ast.TInt] Ast.TInt);
    "sub",
      Ast.EExtern ("sub", EffPure, Ast.t_arrow [Ast.TInt; Ast.TInt] Ast.TInt);
    "mult",
      Ast.EExtern ("mult", EffPure, Ast.t_arrow [Ast.TInt; Ast.TInt] Ast.TInt);
    "div",
      Ast.EExtern ("div", EffPure, Ast.t_arrow [Ast.TInt; Ast.TInt] Ast.TInt);
      (* Sould `div` be pure since it can fail for div_by_zero? *)
    "eq",
      Ast.EExtern ("eq", EffPure, Ast.t_arrow [Ast.TInt; Ast.TInt] Ast.TBool);
    "le",
      Ast.EExtern ("le", EffPure, Ast.t_arrow [Ast.TInt; Ast.TInt] Ast.TBool);
    "and",
      Ast.EExtern ("and", EffPure, Ast.t_arrow [Ast.TBool; Ast.TBool] Ast.TBool);
    "or",
      Ast.EExtern ("or", EffPure, Ast.t_arrow [Ast.TBool; Ast.TBool] Ast.TBool);
    "not",
      Ast.EExtern ("not", EffPure, Ast.t_arrow [Ast.TBool] Ast.TBool);
    "readInt",
      Ast.EExtern ("readInt", EffImpure, Ast.t_arrow [Ast.TUnit] Ast.TInt);
    "printInt",
      Ast.EExtern ("printInt", EffImpure, Ast.t_arrow [Ast.TInt] Ast.TUnit);
    "printAscii",
      Ast.EExtern ("printAscii", EffImpure, Ast.t_arrow [Ast.TInt] Ast.TUnit);
    "printType",
      Ast.EExtern ("printType", EffImpure, Ast.t_arrow [Ast.THole] Ast.TUnit);
  ]

let prepend_prelude ast =
  let f (name, extern) body =
    make @@ Ast.ELet ((name,Ast.THole), make extern, body)
  in
  List.fold_right f builtin_functions ast
