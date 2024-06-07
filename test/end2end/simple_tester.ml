(* simple tester for runing files and checkint output *)


type expected = {
  stdout : string list;
  stderr : string list;
  exit_code : int;
  loops : bool;
}

let collect_metadata fd =
  let loops = ref false in
  let exit_code = ref 0 in
  let filter_meta line =
    if not (String.starts_with ~prefix:"//@" line)
    then None
    else
      let remove_prefix prefix s = 
        let l = String.length prefix in
        String.sub line l (String.length line - l) |> String.trim in
      let command =
        remove_prefix "//@" line |> String.lowercase_ascii in
      if String.starts_with ~prefix:"stdout:" command
      then
        Some (Either.Left (remove_prefix "stdout:" command))
      else if String.starts_with ~prefix:"stderr:" command
      then
        Some (Either.Right (remove_prefix "stderr:" command))
      else if String.starts_with ~prefix:"loops:" command
      then (
        loops := remove_prefix "error:" command |> bool_of_string;
        None)
      else if String.starts_with ~prefix:"error:" command
      then (
        exit_code := remove_prefix "error:" command |> int_of_string;
        None)
      else (
        Printf.eprintf "Warining: Unexpected meta command [%s]" command;
        None)
  in
  let to_two_lists (seq : ('a, 'b) Either.t Seq.t) =
    let rec inner (stdout, strerr) seq =
      match seq() with
      | Seq.Nil -> List.rev stdout, List.rev strerr
      | Seq.Cons(Either.Left str, seq) ->
        inner (str :: stdout, strerr) seq
      | Seq.Cons(Either.Right str, seq) ->
        inner (stdout, str :: strerr) seq
    in inner ([], []) seq
  in
  let expected_stdout, expected_stderr =
    Seq.of_dispenser (fun () -> In_channel.input_line fd)
    |> Seq.filter_map filter_meta
    |> to_two_lists in
  { stdout=expected_stdout;
    stderr=expected_stderr;
    loops=(!loops);
    exit_code=(!exit_code);
  }

(* -------------------------------------------------------------------------- *)

type child = {
  pid : int;
  stdin  : out_channel;
  stdout : in_channel;
  stderr : in_channel;
}

let run_program exec file args =
  let args' = Array.append [| file |] args in
  let stdout, stdin, stderr as channels = Unix.open_process_full exec args' in
  let pid = Unix.process_full_pid channels in
  { pid; stdin; stdout; stderr; }

(* -------------------------------------------------------------------------- *)

let failed = ref false

let assert_all_output expected where =
  if List.is_empty expected then () else
  Printf.eprintf
    "Error: More output expected: expected more output on %s\n" where;
  failed := true

let handle_exit (expected : expected) child_pid =
  Unix.kill child_pid Sys.sigterm;
  let _, proc_status = Unix.waitpid [WNOHANG] child_pid in
  assert_all_output expected.stdout "stdout";
  assert_all_output expected.stderr "stderr";
  begin match proc_status with
  | WEXITED code ->
    if code = expected.exit_code then () else
    Printf.eprintf
      "Error: Unexpected exit code: expected program to exit with %d
      , but gotten %d instead.\n"
      expected.exit_code code;
    failed := true
  | WSIGNALED s ->
    if s = Sys.sigterm && expected.loops then () else
    if not expected.loops then (
      Printf.eprintf "Error: Program did not terminate as expected.\n";
      failed := true)
    else (
      Printf.eprintf
        "Error: Program killed by unexpected signal [%d].\n" s;
      failed := true)
  | WSTOPPED _ -> failwith "unexpected handle_exit case"
  end

let check_line expected actual =
  if expected = actual
  then ()
  else (
    Printf.eprintf
      "Error: Output missmatch:\nExpected: %s\nActual: %s\n"
      expected actual;
    failed := true)

let readline fd =
  match In_channel.input_line fd with
  | Some s -> String.trim s
  | None -> failwith
    "internal error, select returned fd as ready to read
    , but reading failed"

let loop_inside program =
  let stdout = Unix.descr_of_in_channel program.stdout in
  let stderr = Unix.descr_of_in_channel program.stdout in
  fun expected ->
  let _, ready_read, _ = Unix.select [] [stdout; stderr] [] 5.0 in
  let handle_fd (expected, _ : expected * bool) fd =
    begin match expected.stdout, expected.stderr with
    | l :: ls, _ when fd = stdout ->
      let line = readline program.stdout in
      check_line l line;
      { expected with stdout=ls }
    | [], _ when fd = stdout ->
      let line = readline program.stdout in
      Printf.eprintf "Warning: unexpected print on stdout: %s"
          line;
      expected
    | _, l :: ls when fd = stderr ->
      let line = readline program.stderr in
      check_line l line;
      { expected with stderr=ls }
    | [], _ when fd = stderr ->
      let line = readline program.stderr in
      Printf.eprintf "Warning: unexpected print on stderr: %s"
          line;
      expected
    | _ -> failwith "impossible"
    end, true
  in
  List.fold_left handle_fd (expected, false) ready_read

let loop loopable expected =
  let rec inner expected =
    let expected', continue = loopable expected in
    if continue
    then inner expected'
    else expected'
  in
  handle_exit (inner expected)

let test_prog exec file args =
  let expected = In_channel.with_open_text file collect_metadata in
  let program = run_program exec file args in
  loop (loop_inside program) expected program.pid

(* ========================================================================== *)

let _ =
  if Array.length Sys.argv >= 3 then
    Printf.eprintf "Usage: %s EXEC FILE [ARGS]\n" Sys.argv.(0)
  else (
    test_prog
      Sys.argv.(1)
      Sys.argv.(2)
      (Array.sub Sys.argv 3 (Array.length Sys.argv - 3));
    if !failed then (
      Printf.eprintf "Test failed [%s]" Sys.argv.(2);
      exit 1))



