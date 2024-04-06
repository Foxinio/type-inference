(** The main module of a inerpreter *)

open Prototyp_lib
open Core

let check_invariant f p =
  f p;
  p

let pipeline (fname : string) =
  let _ = fname
  |> Parser.parse_file
  |> Imast.translate_to_IMAst
  |> Typing.infer in
  (* |> SystemF.to_system_f *)
  (* |> check_invariant SystemF.ensure_well_typed *)
  (* |> Eval.eval_program *)
  ()

let _ =
  if Array.length Sys.argv <> 2 then
    Printf.eprintf "Usage: %s FILE\n" Sys.argv.(0)
  else
    try pipeline Sys.argv.(1) with
    | Utils.Fatal_error -> exit 1
