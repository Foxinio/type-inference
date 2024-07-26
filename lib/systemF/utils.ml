open Core


let report_type_missmatch ?(env=Env.empty) tp1 tp2 =
  let tstr1 = PrettyPrinter.pp_type (Env.get_ctx env) tp1 in
  let tstr2 = PrettyPrinter.pp_type (Env.get_ctx env) tp2 in
  Utils.report_internal_error "Type missmatch, expected: [%s], actual [%s]" tstr1 tstr2

let report_unexpected_type ?(env=Env.empty) tp expected =
  let tstr = PrettyPrinter.pp_type (Env.get_ctx env) tp in
  Utils.report_internal_error "Unexpected type: [%s], expected [%s]" tstr expected

let report_unbound_tvar () =
  Utils.report_internal_error "SystemF: unbound tvar"

let report_too_many_arguments () =
  Utils.report_internal_error "Application with too many arguments"

let report_not_enough_arguments () =
  Utils.report_internal_error "Application with not enough arguments"
