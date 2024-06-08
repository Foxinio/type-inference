open Imast

(* ========================================================================== *)

let prelude_pos = { Lexing.dummy_pos with pos_fname="Prelude" }

let make data : ('a, 'b) Ast.node =
  { data; typ=Ast.THole; start_pos=prelude_pos; end_pos=prelude_pos }

module StringMap = Map.Make(String)

let builtin_functions = [
    "add",
      Ast.EExtern ("add", Ast.TArrow([Ast.TInt; Ast.TInt], Ast.TInt));
    "sub",
      Ast.EExtern ("sub", Ast.TArrow([Ast.TInt; Ast.TInt], Ast.TInt));
    "mult",
      Ast.EExtern ("mult", Ast.TArrow([Ast.TInt; Ast.TInt], Ast.TInt));
    "div",
      Ast.EExtern ("div", Ast.TArrow([Ast.TInt; Ast.TInt], Ast.TInt));
    "eq",
      Ast.EExtern ("eq", Ast.TArrow([Ast.TInt; Ast.TInt], Ast.TBool));
    "le",
      Ast.EExtern ("le", Ast.TArrow([Ast.TInt; Ast.TInt], Ast.TBool));
    "not",
      Ast.EExtern ("not", Ast.TArrow([Ast.TBool], Ast.TBool));
    "printInt",
      Ast.EExtern ("printInt", Ast.TArrow([Ast.TInt], Ast.TUnit));
    "printAscii",
      Ast.EExtern ("printAscii", Ast.TArrow([Ast.TInt], Ast.TUnit));
    "printType",
      Ast.EExtern ("printType", Ast.TArrow([Ast.THole], Ast.TUnit));
  ]

let prepend_prelude ast =
  let f (name, extern) body =
    make @@ Ast.ELet ((name,Ast.THole), make extern, body)
  in
  List.fold_right f builtin_functions ast
