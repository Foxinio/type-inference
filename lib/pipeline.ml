module Core = Core
module Core_parser = Core_parser
module ToImast = ToImast
module Typing = Typing
module ToSystemF = ToSystemF
module SystemF = SystemF
module Erase = Erase
module Eval = Eval

open Core

let check_invariant f p =
  f p;
  p

let analyze = ref true

let maybe_transform f =
  if !analyze then f else Fun.id

let dump stage pp p =
  let str = pp p in
  Printf.eprintf "[%s] passed\n%!" stage;
  let wall = String.make 40 '#' in
  Printf.eprintf "%s\n%s\n%s\n%!" wall str wall;
  p

let mark stage p =
  Printf.eprintf "[%s] reached\n%!" stage;
  p


let pipeline (fname : string) =
  let _ = fname
  |> Core_parser.parse_file
  |> Builtin.handle_buildins
  |> ToImast.translate
  |> mark "inference"
  |> Typing.infer
  |> ToSystemF.tr_program
  |> dump "toSystemF" SystemF.pp_program
  |> maybe_transform SystemF.transform_with_effects
  |> dump "tr_with_effects"SystemF.pp_program
  |> maybe_transform SystemF.transform_with_folding
  |> dump "tr_with_folds" SystemF.pp_program
  |> check_invariant SystemF.ensure_well_typed
  |> dump "ensure_well_typed" SystemF.pp_program
  |> mark "type erasure"
  |> Erase.erase_type
  |> Eval.eval_program
  in ()

let test_file = "../../../test/end2end/tests/005_polymorphism.lm" 
