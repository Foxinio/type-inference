open Core
module VarTbl = Imast.VarTbl

let dump_type2 env sep tp1 tp2 =
  let str1 = PrettyPrinter.pp_type tp1 in
  let str2 = PrettyPrinter.pp_type tp2 in
  Printf.eprintf "[%s%s%s]\n%!" str1 sep str2

let dump_type env tp =
  let str = PrettyPrinter.pp_type tp in
  Printf.eprintf "[%s]\n%!" str

let dump_expr env e =
  let string_of_type tp = PrettyPrinter.pp_type tp in
  let str = Core.Imast.string_of_expr e VarTbl.find string_of_type in
  Printf.eprintf "%s\n%!" str


let counter = ref 0
let mark stage =
  Printf.eprintf "[%d] %s\n%!" !counter stage;
  incr counter

let unwrap (node : Imast.expl_type Imast.expr) env var opt =
  let open Core.Imast in
  match opt with
  | Some t -> t
  | None ->
    let string_of_var var = Printf.sprintf "{%s;%s}"
      (IMAstVar.to_string var) (VarTbl.find var) in
    let name = string_of_var var in
    let string_of_type _ = "(typ)" in
    let str = Core.Imast.string_of_expr node string_of_var string_of_type in
    let env_str = Env.pp_env env in
    Utils.report_error node "Undefined variable: %s in %s\n\nEnv: %s" name str env_str

