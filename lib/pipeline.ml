module Core = Core
module LmParser = LmParser
module ToImast = ToImast
module Typing = Typing
module ToSystemF = ToSystemF
module SystemF = SystemF
module Erase = Erase
module Eval = Eval

open LmConfig

open Core

let stage_counter = ref 0
let stages = [|
  "Parser";
  "Builtin insert";
  "ToImast translation";
  "Type inference";
  "ToSystemF translation";
  "Effect analysis";
  "Folding analysis";
  "WellTyped checking";
  "Type erasure";
  "Erase";
  "Eval";
|]

let mark transform p =
  let p' = transform p in
  let stage = stages.(!stage_counter) in
  Utils.mark_stage "[%s] Passed" stage;
  incr stage_counter;
  p'

let transform2 cond f1 f2 =
  let f = if cond then f1 else f2 in
  mark f

let check_invariant f p =
  f p;
  mark Fun.id p

let dump pp p =
  let str = pp p in
  Utils.dump_ast str;
  p

let print_internal_error fmt =
  let f s =
    if !LmConfig.verbose_internal_errors
    then (
      Printf.eprintf "%s" s;
      Printexc.print_backtrace stderr)
    else Printf.eprintf "Internal error\n"
  in Printf.ksprintf f fmt

let pipeline (fname : string) =
  let open Core.Utils in
  try fname
  |> mark LmParser.parse_file 

  |> mark Builtin.handle_buildins

  |> mark ToImast.translate
  |> dump Imast.pp_program

  |> mark Typing.infer
  |> dump Typing.PrettyPrinter.pp_expr

  |> mark ToSystemF.tr_program
  |> dump SystemF.pp_program

  |> transform2 !LmConfig.use_analysis
      SystemF.transform_with_effects
      SystemF.crude_transform_with_effects
  |> dump SystemF.pp_program

  |> transform2 !LmConfig.use_analysis
      SystemF.transform_with_folding
      SystemF.crude_transform_with_folding
  |> dump SystemF.pp_program

  |> check_invariant SystemF.ensure_well_typed
  |> dump SystemF.pp_program

  |> mark Erase.erase_type
  |> dump Erase.pp_program

  |> mark Eval.eval_program
  with
  | Assert_failure (fname, line, char) -> (
    print_internal_error "Assertion failed at: %s:%d:%d\n%!" fname line char;
    Utils.mark_stage "[%s] Reached" stages.(!stage_counter);
    exit 1
    )
  | Exit ->
    Utils.mark_stage "[%s] Reached" stages.(!stage_counter);
    exit 1
  | e -> (
    print_internal_error "Exception thrown: %s\n" (Printexc.to_string e);
    Utils.mark_stage "[%s] Reached" stages.(!stage_counter);
    exit 1
    )

