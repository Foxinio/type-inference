open Imast

(* ========================================================================== *)

let prelude_pos = { Lexing.dummy_pos with pos_fname="Prelude" }

let make data : ('a, 'b) Ast.node =
  { data; typ=Ast.THole; start_pos=prelude_pos; end_pos=prelude_pos }

module StringMap = Map.Make(String)

let builtin_functions = [
    "add",
      Ast.EExtern ("add", Ast.TArrow(Pure, [Ast.TInt; Ast.TInt], Ast.TInt), Ast.THole);
    "sub",
      Ast.EExtern ("sub", Ast.TArrow(Pure, [Ast.TInt; Ast.TInt], Ast.TInt), Ast.THole);
    "mult",
      Ast.EExtern ("mult", Ast.TArrow(Pure, [Ast.TInt; Ast.TInt], Ast.TInt), Ast.THole);
    "div",
      Ast.EExtern ("div", Ast.TArrow(Pure, [Ast.TInt; Ast.TInt], Ast.TInt), Ast.THole);
      (* Sould `div` be pure since it can fail for div_by_zero? *)
    "eq",
      Ast.EExtern ("eq", Ast.TArrow(Pure, [Ast.TInt; Ast.TInt], Ast.TBool), Ast.THole);
    "le",
      Ast.EExtern ("le", Ast.TArrow(Pure, [Ast.TInt; Ast.TInt], Ast.TBool), Ast.THole);
    "and",
      Ast.EExtern ("and", Ast.TArrow(Unknown, [Ast.TBool; Ast.TBool], Ast.TBool), Ast.THole);
    "or",
      Ast.EExtern ("or", Ast.TArrow(Unknown, [Ast.TBool; Ast.TBool], Ast.TBool), Ast.THole);
    "not",
      Ast.EExtern ("not", Ast.TArrow(Pure, [Ast.TBool], Ast.TBool), Ast.THole);
    "readInt",
      Ast.EExtern ("readInt", Ast.TArrow(Impure, [Ast.TUnit], Ast.TInt), Ast.THole);
    "printInt",
      Ast.EExtern ("printInt", Ast.TArrow(Impure, [Ast.TInt], Ast.TUnit), Ast.THole);
    "printAscii",
      Ast.EExtern ("printAscii", Ast.TArrow(Impure, [Ast.TInt], Ast.TUnit), Ast.THole);
    "printType",
      Ast.EExtern ("printType", Ast.TArrow(Impure, [Ast.THole], Ast.TUnit), Ast.THole);
  ]

let prepend_prelude ast =
  let f (name, extern) body =
    make @@ Ast.ELet ((name,Ast.THole), make extern, body)
  in
  List.fold_right f builtin_functions ast
