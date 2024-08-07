open Core
open Imast

open PrettyPrinter

let report_type_missmatch tp1 tp2 =
  let tstr1 = pp_type tp1 in
  let tstr2 = pp_type tp2 in
  Utils.report_internal_error
    "Type missmatch, expected: [%s], actual [%s]" tstr1 tstr2

let report_unexpected_type tp expected =
  let tstr = pp_type tp in
  Utils.report_internal_error
    "Unexpected type: [%s], expected [%s]" tstr expected

let report_unbound_tvar () =
  Utils.report_internal_error "SystemF: unbound tvar"

let report_too_many_arguments () =
  Utils.report_internal_error "Application with too many arguments"

let report_not_enough_arguments () =
  Utils.report_internal_error "Application with not enough arguments"

(* =========================================================================== *)
(* Debug utils *)

let debug = Utils2.debug
let mark = Utils2.mark
let counter = Utils2.counter

let dump_type2 sep tp1 tp2 =
  let str1 = pp_type tp1 in
  let str2 = pp_type tp2 in
  debug "[%s%s%s]" str1 sep str2

let dump_type tp =
  let str = pp_type tp in
  debug "[%s]" str

let dump_expr env e =
  let env = Env.to_env2 env in
  let str = pp_expr env e in
  debug "%s" str

let pp_syn_type =
  let string_of_tvar x = pp_lookup_tvar x in
  let rec pp_vars = function
    | [] -> ""
    | x :: xs -> VarTbl.find x^", "^pp_vars xs
  and pp_tvars = function
    | [] -> ""
    | x :: xs -> string_of_tvar x^" "^pp_tvars xs
  in function
  | Main.EUnit -> "EUnit"
  | Main.EBool b -> "EBool "^string_of_bool b
  | Main.ENum i -> "ENum "^string_of_int i
  | Main.EVar x -> "EVar "^VarTbl.find x
  | Main.EFn (xs, _, _) -> "EFn ("^pp_vars xs^")"
  | Main.EFix (f, xs, _, _) -> "EFix "^VarTbl.find f^"("^pp_vars xs^")"
  | Main.EApp (_, _) -> "EApp"
  | Main.ETFn (xs, _) -> "ETFn "^pp_tvars xs^"."
  | Main.ETApp (_, _) -> "ETApp"
  | Main.ELet (x, _, _) -> "ELet "^VarTbl.find x
  | Main.EExtern (name, _) -> "EExtern "^name
  | Main.EPair (_, _) -> "EPair"
  | Main.EFst _ -> "EFst"
  | Main.ESnd _ -> "ESnd"
  | Main.EIf (_, _, _) -> "EIf"
  | Main.ESeq (_, _) -> "ESeq"
  | Main.EType (_, _, _, _) -> "EType"
  | Main.ECtor (name, tps, _) ->
    let tps' = List.map pp_type tps |> String.concat ", " in
    "ECtor "^VarTbl.find name^"["^tps'^"]"
  | Main.EMatch (_, _, _) -> "EMatch"


let add_map a b =
  mark "[%s ~> %s]"
    (pp_lookup_tvar a)
    (pp_lookup_tvar b);

