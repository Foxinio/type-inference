module Core = Core
module Core_parser = Core_parser
module ToImast = ToImast
module Typing = Typing
module ToSystemF = ToSystemF
module SystemF = SystemF
module Erase = Erase
module Eval = Eval

open LmConfig

open Core

let check_invariant f p =
  f p;
  p

let maybe_transform cond f =
  if cond then f else Fun.id

let transform2 cond f1 f2 =
  if cond then f1 else f2

let dump pp p =
  let str = pp p in
  Utils.dump_ast str;
  p

let mark stage p =
  Utils.mark_stage "[%s] Passed" stage;
  p


let pipeline (fname : string) =
  let open Core.Utils in
  try fname
  |> Core_parser.parse_file
  |> mark "Parser"

  |> Builtin.handle_buildins
  |> mark "Builtin insert"

  |> ToImast.translate
  |> mark "ToImast translation"

  |> Typing.infer
  |> mark "Type inference"
  |> dump Typing.PrettyPrinter.pp_expr

  |> ToSystemF.tr_program
  |> mark "ToSystemF translation"
  |> dump SystemF.pp_program

  |> transform2 !LmConfig.use_analysis
      SystemF.transform_with_effects
      SystemF.crude_transform_with_effects
  |> mark "Effect analysis"
  |> dump SystemF.pp_program

  |> transform2 !LmConfig.use_analysis
      SystemF.transform_with_folding
      SystemF.crude_transform_with_folding
  |> mark "Effect analysis"
  |> dump SystemF.pp_program

  |> check_invariant SystemF.ensure_well_typed
  |> mark "WellTyped checking"
  |> dump SystemF.pp_program

  |> Erase.erase_type
  |> mark "Type erasure"

  |> Eval.eval_program
  with
  | Syntax_error str ->
    Printf.eprintf "Syntax error: %s\n%!" str;
    exit 1
  | Fatal_error str ->
    Printf.eprintf "Fatal error: %s\n%!" str;
    exit 1
  | Internal_error str ->
    if !LmConfig.verbose_internal_errors
    then Printf.eprintf "Internal error: %s\n%!" str
    else Printf.eprintf "Internal error\n";
    exit 1
  | Runtime_error str ->
    Printf.eprintf "Runtime error: %s\n%!" str;
    exit 1
  | Assert_failure (fname, line, char) ->
    if !LmConfig.verbose_internal_errors
    then Printf.eprintf "Assertion failed at: %s:%d:%d\n%!" fname line char
    else Printf.eprintf "Internal error\n";
    exit 1
  | e ->
    if !LmConfig.verbose_internal_errors
    then Printf.eprintf "Unknown exception thrown\n"
    else Printf.eprintf "Internal error\n";
    exit 1
