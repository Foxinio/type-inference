(** The main module of a interpreter *)

open Pipeline
open Core

let help_msg = Printf.sprintf {|
  Usage: %s [-a|-s|-c] FILE

  -a - use analysis
  -c - crude analysis (mark all arrows impure)
  -s - skip analysis

|} Sys.argv.(0)

let main () =
  if Array.length Sys.argv <> 3 then
    (Printf.eprintf "%s"  help_msg;
    exit 1)
  else
    (if Sys.argv.(1) = "-a" then
      analyze := true
    else if Sys.argv.(1) = "-s" then
      analyze := false
    else
      (Printf.eprintf "Usage: %s [-a|-s] FILE\n%s" Sys.argv.(0) help_msg;
      exit 1));
    try pipeline Sys.argv.(2) with
    | Utils.Fatal_error -> exit 1


let _ =
  Printexc.record_backtrace true;
  try main () with e ->
    let msg = Printexc.to_string e
    and stack = Printexc.get_backtrace () in
      Printf.eprintf "there was an error: %s\n%s\n" msg stack
