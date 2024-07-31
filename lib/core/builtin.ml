open Imast
open Effect

(* ========================================================================= *)

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
  "not",
    Ast.EExtern ("not", EffPure, Ast.t_arrow [Ast.TBool] Ast.TBool);
  "readInt",
    Ast.EExtern ("readInt", EffImpure, Ast.t_arrow [Ast.TUnit] Ast.TInt);
  "printInt",
    Ast.EExtern ("printInt", EffImpure, Ast.t_arrow [Ast.TInt] Ast.TUnit);
  "printAscii",
    Ast.EExtern ("printAscii", EffImpure, Ast.t_arrow [Ast.TInt] Ast.TUnit);
]

let prepend_prelude ast =
  let f (name, extern) body =
    make @@ Ast.ELet ((name,Ast.THole), make extern, body)
  in
  List.fold_right f builtin_functions ast

let subst_dependent = [
  "and",
    Ast.EExtern ("and", EffPure, Ast.t_arrow [Ast.TBool; Ast.TBool] Ast.TBool);
  "or",
    Ast.EExtern ("or", EffPure, Ast.t_arrow [Ast.TBool; Ast.TBool] Ast.TBool);
  "printType",
    Ast.EExtern ("printType", EffImpure, Ast.t_arrow [Ast.THole] Ast.TUnit);
]

let subst_prelude ast =
  let rec inner env (e : 'a Ast.expr) =
    match e.data with
    | EUnit | ENum _ | EBool _ | EExtern _ -> e.data
    | EVar (name, tps) ->
      begin match StringMap.find_opt name env with
        | Some extern -> extern
        | None -> e.data
      end
    | EFn (var, body) -> EFn (var, subst env body)
    | EFix (var, arg, body) -> EFix (var, arg, subst env body)
    | EApp (fn, arg) -> EApp (subst env fn, subst env arg)
    | ELet (var, def, body) -> ELet (var, subst env def, subst env body)
    | EPair (a, b) -> EPair (subst env a, subst env b)
    | EFst e -> EFst (subst env e)
    | ESnd e -> ESnd (subst env e)
    | EIf (a, b, c) -> EIf (subst env a, subst env b, subst env c)
    | ESeq (a, b) -> ESeq (subst env a, subst env b)
    | ETypeAlias (a, b, c) -> ETypeAlias (a, b, subst env c)
    | EType (a, b, c) -> EType (a, b, subst env c)
    | ECtor (a, b) -> ECtor (a, subst env b)
    | EMatch (a, b) -> EMatch (subst env a, List.map (subst_clause env) b)
  and subst_clause env (name, var, e) =
    name, var, subst env e
  and subst env e =
    let data = inner env e in
    { e with data }
  in
  let env = StringMap.of_list subst_dependent in
  subst env ast

let handle_buildins ast =
  let ast = subst_prelude ast in
  let ast = prepend_prelude ast in
  ast
