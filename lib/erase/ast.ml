(* Ast data definitions and helper functions *)

open Core

exception RuntimeError of string

type var       = Imast.IMAstVar.t
type ctor_name = int

type value =
  | VUnit
  | VInt  of int
  | VBool of bool
  | VPair of value * value
  | VADT  of ctor_name * value
  | VClo  of (value list -> value)

and expr =
  | EUnit
  | EBool   of bool
  | ENum    of int
  | EVar    of var
  | EExtern of (value list -> value)
  | EFn     of var list * expr
  | EFix    of var * var list * expr
  | EApp    of expr * expr list
  | ELet    of var * expr * expr
  | EPair   of expr * expr
  | EIf     of expr * expr * expr
  | ESeq    of expr * expr
  | ECtor   of ctor_name * expr
  | EMatch  of expr * clause array

and clause = var * expr

type program = expr

let unimplemented () = failwith "unimplemented"

(* ========================================================================= *)
(* Pretty printing functions *)

open Printf
module VarTbl = Core.Imast.VarTbl

let pp_at_level l lvl str =
  if lvl > l then sprintf "(%s)" str
  else str

let endline indent str =
  sprintf "\n%s%s" indent str

let endline' indent str =
  sprintf "\n  %s%s" indent str

let fun_lvl = 0
let tapp_lvl = 1
let app_lvl = 2
let def_lvl = 3
let pair_lvl = 4
let if_lvl = 5
let seq_lvl = 6
let match_lvl = 7

let rec pp_expr (indent : string) (lvl : int) : expr -> string = function
  | EUnit -> "()"
  | EBool b -> string_of_bool b
  | ENum n -> string_of_int n
  | EVar x -> VarTbl.find x

  | EFn (xs, body) ->
    let vars = List.map VarTbl.find xs in
    let body_str = pp_expr (indent^"  ") fun_lvl body in
    pp_at_level fun_lvl lvl
      (sprintf "fun %s =>%s"
        (String.concat " " vars)
        (endline' indent body_str))

  | EFix (f, xs, body) ->
    let vars = List.map VarTbl.find xs in
    let body_str = pp_expr (indent^"  ") fun_lvl body in
    pp_at_level fun_lvl lvl
      (sprintf "fix %s %s =>%s"
        (VarTbl.find f)
        (String.concat " " vars)
        @@ endline' indent body_str)

  | EApp(e1, es) ->
    pp_app indent lvl e1 es

  | ELet (x, e1, e2) ->
    let e1' = pp_expr (indent^"  ") def_lvl e1 in
    let e2 = pp_expr indent def_lvl e2 in
    pp_at_level def_lvl lvl
      (sprintf "let %s =%s%s%s"
        (VarTbl.find x)
        (endline' indent e1')
        (endline indent "in")
        (endline indent e2))

  | EExtern _ ->
    sprintf "(extern)"

  | EPair(e1, e2) ->
    let e1str = pp_expr (indent^"  ") pair_lvl e1 in
    let e2str = pp_expr (indent^"  ") pair_lvl e2 in
    pp_at_level pair_lvl lvl
      (sprintf "%s, %s" e1str e2str)

  | EIf (cond, e1, e2) ->
    let condstr = pp_expr (indent^"  ") if_lvl cond in
    let e1str = pp_expr (indent^"  ") if_lvl e1 in
    let e2str = pp_expr (indent^"  ") if_lvl e2 in
    pp_at_level if_lvl lvl
      (sprintf "if %s%s%s"
        condstr
        (endline indent @@ sprintf "then %s" e1str)
        (endline indent @@ sprintf "else %s" e2str))

  | ESeq (e1, e2) ->
    let e1str = pp_expr (indent^"  ") seq_lvl e1 in
    let e2str = pp_expr (indent^"  ") seq_lvl e2 in
    pp_at_level seq_lvl lvl
      (sprintf "%s;%s" e1str @@ endline indent e2str)

  | ECtor (name, body) ->
    let bodystr = pp_expr (indent^"  ") app_lvl body in
    pp_at_level app_lvl lvl
      (sprintf "%d (%s)" name bodystr)

  | EMatch (body, clauses) ->
    let bodystr = pp_expr (indent^"  ") app_lvl body in
    let clausesstr = pp_clauses (indent^"  ") clauses in
    pp_at_level app_lvl lvl
      (sprintf "match %s with%s%s" bodystr clausesstr @@ endline indent "end")

and pp_app indent lvl e1 es =
  let e1str = pp_expr (indent^"  ") app_lvl e1 in
  let f e = pp_expr (indent^"    ") (lvl+1) e in
  let estr = List.map f es
    |> String.concat ("\n  "^indent) in
  pp_at_level (app_lvl-1) lvl
    (sprintf "%s %s" e1str @@ endline indent estr)

and pp_clauses indent clauses =
  let f i (var, body) =
    let var_name = VarTbl.find var in
    let bodystr = pp_expr (indent^"  ") app_lvl body in
    sprintf "| %d %s =>%s" i var_name @@ endline' indent bodystr
  in
  let estrs = Array.to_seq clauses
    |> Seq.mapi f
    |> List.of_seq in
  let sep = "\n"^indent in
  String.concat sep estrs |> endline indent

let pp_program p =
  pp_expr "" 0 p
