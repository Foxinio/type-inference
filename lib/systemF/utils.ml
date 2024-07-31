open Core


let report_type_missmatch tp1 tp2 =
  let tstr1 = PrettyPrinter.pp_type tp1 in
  let tstr2 = PrettyPrinter.pp_type tp2 in
  Utils.report_internal_error
    "Type missmatch, expected: [%s], actual [%s]" tstr1 tstr2

let report_unexpected_type tp expected =
  let tstr = PrettyPrinter.pp_type tp in
  Utils.report_internal_error
    "Unexpected type: [%s], expected [%s]" tstr expected

let report_unbound_tvar () =
  Utils.report_internal_error "SystemF: unbound tvar"

let report_too_many_arguments () =
  Utils.report_internal_error "Application with too many arguments"

let report_not_enough_arguments () =
  Utils.report_internal_error "Application with not enough arguments"


let dump_type2 sep tp1 tp2 =
  let str1 = PrettyPrinter.pp_type tp1 in
  let str2 = PrettyPrinter.pp_type tp2 in
  Utils.debug "[%s%s%s]" str1 sep str2

let dump_type tp =
  let str = PrettyPrinter.pp_type tp in
  Utils.debug "[%s]" str

let dump_expr e =
  let str = PrettyPrinter.pp_expr e in
  Utils.debug "%s" str


let counter = ref 0
let mark stage =
  Utils.debug "[%d] %s" !counter stage;
  incr counter

