(** simple tester for runing files and checkint output *)


type expected = {
  stdout : string list;
  stderr : string list;
  exit_code : int;
  loops : bool;
}

let collect_metadata fd =
  let remove_prefix prefix s = 
    let l = String.length prefix in
    String.sub s l (String.length s - l) |> String.trim in
  let loops = ref false in
  let exit_code = ref 0 in
  let filter_meta line =
    if not (String.starts_with ~prefix:"//@" line)
    then None
    else
      let command = remove_prefix "//@" line |> String.lowercase_ascii in
      if String.starts_with ~prefix:"stdout:" command
      then
        Some (Either.Left (remove_prefix "stdout:" command))
      else if String.starts_with ~prefix:"stderr:" command
      then
        Some (Either.Right (remove_prefix "stderr:" command))
      else if String.starts_with ~prefix:"loops:" command
      then (
        loops := remove_prefix "loops:" command |> bool_of_string;
        None)
      else if String.starts_with ~prefix:"code:" command
      then (
        exit_code := remove_prefix "code:" command |> int_of_string;
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

(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)

let failed = ref false

let assert_all_output expected where =
  if List.is_empty expected then () else (
  Printf.eprintf
    "Error: More output expected: expected more output on %s\n" where;
  failed := true)

let handle_exit (expected : expected) proc_status =
  assert_all_output expected.stdout "stdout";
  assert_all_output expected.stderr "stderr";
  begin match proc_status with
  | Unix.WEXITED code ->
    if code = expected.exit_code then () else (
    Printf.eprintf
      "Error: Unexpected exit code: expected program to exit with %d
      , but gotten %d instead.\n"
      expected.exit_code code;
    failed := true)
  | Unix.WSIGNALED s ->
    if s = Sys.sigkill && expected.loops then () else (
    if not expected.loops then (
      Printf.eprintf "Error: Program did not terminate as expected.\n";
      failed := true)
    else (
      Printf.eprintf
        "Error: Program killed by unexpected signal [%d].\n" s;
      failed := true))
  | Unix.WSTOPPED _ -> failwith "unexpected handle_exit case"
  end

(* ------------------------------------------------------------------------- *)

let check_line expected actual =
  if Str.string_match (Str.regexp_string expected) actual 0
  then ()
  else (
    Printf.eprintf
      "Error: Output missmatch:\nExpected: %s\nActual: %s\n"
      expected actual;
    failed := true)

let readline_and_check expected fd =
  match In_channel.input_line fd with
  | Some s ->
    let actual = String.trim s |> String.lowercase_ascii in
    check_line expected actual;
    []
  | None -> [expected]

let readline fd =
  match In_channel.input_line fd with
  | Some s -> String.trim s |> String.lowercase_ascii
  | None -> failwith
    "internal error, select returned fd as ready to read
    , but reading failed"

let loop_inside program =
  let stdout = Unix.descr_of_in_channel program.stdout in
  let stderr = Unix.descr_of_in_channel program.stdout in
  fun expected finished ->
  let delay = if finished then 0.0 else 5.0 in
  let _, ready_read, _ = Unix.select [] [stdout; stderr] [] delay in
  let handle_fd (expected, _ : expected * bool) fd =
    begin match expected.stdout, expected.stderr with
    | l :: ls, _ when fd = stdout ->
      let ls = readline_and_check l program.stdout @ ls in
      { expected with stdout=ls }
    | [], _ when fd = stdout ->
      let line = readline program.stdout in
      Printf.eprintf "Warning: unexpected print on stdout: %s" line;
      expected
    | _, l :: ls when fd = stderr ->
      let ls = readline_and_check l program.stderr @ ls in
      { expected with stderr=ls }
    | _, [] when fd = stderr ->
      let line = readline program.stderr in
      Printf.eprintf "Warning: unexpected print on stderr: %s" line;
      expected
    | _ -> failwith "impossible"
    end, true
  in
  List.fold_left handle_fd (expected, false) ready_read

let loop ~check_loop loopable expected child_pid =
  let rec inner expected =
    let pid, proc_status = Unix.waitpid [WNOHANG] child_pid in
    let finished = pid<>0 in
    if finished then
      after_finished expected proc_status
    else (
      let expected', continue = loopable expected finished in
      let pid, proc_status = Unix.waitpid [WNOHANG] child_pid in
      let finished = pid<>0 in
      match continue, finished with
      | true, false -> inner expected'
      | true, true  -> after_finished expected' proc_status
      | false, false when expected'.loops ->
        Unix.kill child_pid Sys.sigkill;
        handle_exit expected' proc_status
      | false, false ->
        Unix.kill child_pid Sys.sigkill;
        Printf.eprintf
          "Error: Program did not terminate as expected, killing.\n";
        failed := true;
        handle_exit expected' proc_status
      | false, true ->
      handle_exit expected' proc_status
    )
  and after_finished expected proc_status =
    let expected', continue = loopable expected true in
    if continue
    then after_finished expected' proc_status
    else handle_exit expected' proc_status
  in
  if check_loop then
    inner expected
  else
    let pid, proc_status = Unix.waitpid [] child_pid in
    after_finished expected proc_status


let test_prog ?(check_loop=false) exec file args =
  let expected = In_channel.with_open_text file collect_metadata in
  if expected.loops && not check_loop then (
    Printf.eprintf ("Test skipped [%s]\n" ^^
      "  (test loops, but looping not being tested)\n%!") file;
    exit 0);
  let program = run_program exec file args in
  loop ~check_loop (loop_inside program) expected program.pid;
  match !failed with
  | true ->
    Printf.eprintf "Test failed  [%s]\n" file;
    exit 1
  | false ->
    Printf.eprintf "Test passed  [%s]\n" file

(* ========================================================================= *)

let main () =
  if Array.length Sys.argv < 2 then (
    Printf.eprintf "Usage: %s EXEC FILE [ARGS]\n" Sys.argv.(0)
  ) else (
    if Sys.argv.(1) = "-check-loop" then (
      Printf.printf "check loop enabled\n%!";
      test_prog ~check_loop:true Sys.argv.(2) Sys.argv.(3)
        (Array.sub Sys.argv 4 (Array.length Sys.argv - 4))
    ) else
      test_prog
        Sys.argv.(1)
        Sys.argv.(2)
        (Array.sub Sys.argv 3 (Array.length Sys.argv - 3))
  )


let _ = main ()
