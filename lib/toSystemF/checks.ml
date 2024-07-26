open SystemF
open Core

let check_arg_amount_correctness xs tapp_args =
  let tapp_len = List.length tapp_args in
  let xs_len = List.length xs in
  if tapp_len <> xs_len
  then Utils.report_internal_error
    ("Wrong number of arguments in type application."^^
    "Expected %d, actual %d") xs_len tapp_len

