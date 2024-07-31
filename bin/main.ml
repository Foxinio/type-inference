(** The main module of a interpreter *)

open Pipeline
open Core
open Arg

let input_file = ref ""

let cmd_args_options = Arg.align
  [ "--print-stages", Arg.Set LmConfig.print_stages,
    " Print stages of the pipeline";

    "--no-print-stages", Arg.Clear LmConfig.print_stages,
    " Do not print stages of the pipeline";

    "--print-env", Arg.Set LmConfig.print_env,
    " Print the environment after WellTyped check";

    "--no-print-env", Arg.Clear LmConfig.print_env,
    " Do not print the environment after WellTyped check";

    "--print-asts", Arg.Set LmConfig.print_asts,
    " Print the ASTs of the pipeline";

    "--no-print-asts", Arg.Clear LmConfig.print_asts,
    " Do not print the ASTs of the pipeline";

    "--add-externs", Arg.Set LmConfig.add_externs,
    " Add externs to the program";

    "--no-externs", Arg.Clear LmConfig.add_externs,
    " Do not add externs to the program";

    "--use-analysis", Arg.Set LmConfig.use_analysis,
    " Use analysis being considered";

    "--crude-analysis", Arg.Clear LmConfig.use_analysis,
    " Use crude analysis";

    "--print-stats", Arg.Set LmConfig.print_stats,
    " Print statistics";

    "--no-print-stats", Arg.Clear LmConfig.print_stats,
    " Do not print statistics";

    "--verbose-internal-errors", Arg.Set LmConfig.verbose_internal_errors,
    " Make internal errors more verbose (for debugging only)";

    "--no-verbose-internal-errors", Arg.Clear LmConfig.verbose_internal_errors,
    " Print less verbose internal errors messages";

    "--debug-log", Arg.Set LmConfig.debug_log,
    " Enable debug logging";

    "--no-debug-log", Arg.Clear LmConfig.debug_log,
    " Disable debug logging";

    "--", Arg.Rest (fun s -> input_file := s),
    "FILE";
  ]

let usage_string =
  Printf.sprintf
    "Usage: %s [OPTION]... FILE \nAvailable OPTIONs are:"
    Sys.argv.(0)

let wrap_excetion f =
  Printexc.record_backtrace true;
  try f () with e ->
    let msg = Printexc.to_string e
    and stack = Printexc.get_backtrace () in
    Printf.eprintf "there was an error: %s\n%s\n" msg stack

let _ =
  Printexc.record_backtrace false;
  Arg.parse cmd_args_options (fun s -> input_file := s) usage_string;
  if !LmConfig.verbose_internal_errors
  then wrap_excetion (fun () -> pipeline !input_file)
  else pipeline !input_file
