(** Utility functions, mostly error reporting *)

let split_list xs n =
  let rec inner acc = function
  | xs, 0 -> List.rev acc, xs
  | x :: xs, n -> inner (x :: acc) (xs, n - 1)
  | [], _ -> failwith "split_list"
  in
  inner [] (xs, n)

let gen_name i =
  let to_ascii x = Char.code 'a' + x |> Char.chr in
  let limit = (Char.code 'z') - (Char.code 'a') + 1 in
  let rec inner i =
    if i >= 0 && i < limit then to_ascii i |> String.make 1 
    else
      let minor = i mod limit |> inner
      and major = i / limit |> pred |> inner in
      major ^ minor
  in
  inner i

let maybe_print cond s =
  if cond
  then Printf.eprintf "%s\n%!" s

let debug fmt =
  Printf.ksprintf (maybe_print !LmConfig.debug_log) fmt

let mark_stage fmt =
  Printf.ksprintf (maybe_print !LmConfig.print_stages) fmt

let dump_ast aststr =
  let wall = String.make 40 '#' in
  Printf.ksprintf (maybe_print !LmConfig.print_asts)
  "%s\n%s\n%s\n" wall aststr wall

let quit _ =
  raise Exit

(** Pretty-printer of locations *)
let string_of_pp (start_p : Lexing.position) (end_p : Lexing.position) =
  if end_p.pos_cnum - start_p.pos_cnum <= 1 then
    Printf.sprintf "file: %s, line:%d, char:%d"
      start_p.pos_fname
      start_p.pos_lnum
      (start_p.pos_cnum - start_p.pos_bol + 1)
  else
    Printf.sprintf "file: %s, line:%d, char:%d-%d"
      start_p.pos_fname
      start_p.pos_lnum
      (start_p.pos_cnum - start_p.pos_bol + 1)
      (end_p.pos_cnum - start_p.pos_bol)

(** report an error not related to any location. *)
let report_error_no_pos fmt =
  Printf.kfprintf
    quit
    stderr
    ("error: " ^^ fmt ^^ "\n")

(** report an error related to a location between given positions. *)
let report_error_pp start_p end_p fmt =
  Printf.kfprintf
    quit
    stderr
    ("%s: error:\n" ^^ fmt ^^ "\n")
    (string_of_pp start_p end_p)

(** report an error related to given AST node, and raise Fatal_error *)
let report_error (node : ('a,'b) Ast.node) fmt =
  report_error_pp node.start_pos node.end_pos fmt

let report_internal_error fmt =
  let f s =
    if !LmConfig.verbose_internal_errors
    then Printf.eprintf "%s" s
    else Printf.eprintf "Internal error\n";
    quit ()
  in Printf.ksprintf
    f
    ("Internal error: " ^^ fmt ^^ "\n")

let report_runtime_error fmt =
  Printf.kfprintf
    quit
    stderr
    ("Runtime error: " ^^ fmt ^^ "\n")
