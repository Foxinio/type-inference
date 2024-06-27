(** The main module of a interpreter *)

open Prototyp_lib
open Core

let check_invariant f p =
  f p;
  p

let pipeline (fname : string) =
  let _ = fname
  |> Core_parser.parse_file
  |> Builtin.prepend_prelude
  |> ToImast.translate
  |> Typing.infer
  |> ToSystemF.tr_program
  |> check_invariant SystemF.ensure_well_typed
  |> Erase.erase_type
  (* |> Eval.eval_program *)
  in ()

let _ =
  if Array.length Sys.argv <> 2 then
    Printf.eprintf "Usage: %s FILE\n" Sys.argv.(0)
  else
    try pipeline Sys.argv.(1) with
    | Utils.Fatal_error -> exit 1
