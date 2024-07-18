(** The main module of a interpreter *)

open Prototyp_lib
open Core

let check_invariant f p =
  f p;
  p

let analyze = ref false

let maybe_transform f =
  if !analyze then f else Fun.id

let pipeline (fname : string) =
  let _ = fname
  |> Core_parser.parse_file
  |> Builtin.prepend_prelude
  |> ToImast.translate
  |> Typing.infer
  |> ToSystemF.tr_program
  |> maybe_transform SystemF.transform_with_effects
  |> maybe_transform SystemF.transform_with_folding
  |> check_invariant SystemF.ensure_well_typed
  |> Erase.erase_type
  (* |> Eval.eval_program *)
  in ()

let help_msg = {|
  -a - use analysis
  -s - skip analysis
|}

let _ =
  if Array.length Sys.argv <> 3 then
    Printf.eprintf "Usage: %s [-a|-s] FILE\n%s" Sys.argv.(0) help_msg
  else
    (if Sys.argv.(1) = "-a" then
      analyze := true
    else if Sys.argv.(1) = "-s" then
      analyze := false
    else
      Printf.eprintf "Usage: %s [-a|-s] FILE\n%s" Sys.argv.(0) help_msg;
    exit 1);
    try pipeline Sys.argv.(1) with
    | Utils.Fatal_error -> exit 1
