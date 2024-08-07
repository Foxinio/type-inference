open Core
module VarTbl = Imast.VarTbl

let debug fmt =
  Utils.debug ("[Typing]"^^fmt)

let ctx = ref None
let get_ctx () =
  match !ctx with
  | None ->
    let ctx' = PrettyPrinter.pp_context () in
    ctx := Some ctx';
    ctx'
  | Some ctx ->
    ctx

let pp_typ typ =
  let ctx = get_ctx() in
  let args = Schema.get_arguments typ |> Type.TVarSet.to_list in
  if List.is_empty args then
    PrettyPrinter.pp_type ~ctx @@ Schema.get_template typ
  else
    Printf.sprintf "(%s)<%s>"
      (PrettyPrinter.pp_type ~ctx @@ Schema.get_template typ)
      (String.concat ", " @@ List.map (PrettyPrinter.pp_lookup_tvar ~ctx) args)

let registered : (string*Schema.typ) list ref = ref []

let register_var (x,tp) =
  registered := (VarTbl.find x, tp) :: !registered

let print_registered () =
  debug "Registered types:";
  List.iter (fun (x,tp) ->
    debug "  %s : %s" x (pp_typ tp))
    !registered

let dump_type2 sep tp1 tp2 =
  let ctx = get_ctx () in
  let str1 = PrettyPrinter.pp_type ~ctx tp1 in
  let str2 = PrettyPrinter.pp_type ~ctx tp2 in
  debug "[%s%s%s]" str1 sep str2

let dump_type tp =
  let ctx = get_ctx () in
  let str = PrettyPrinter.pp_type ~ctx tp in
  debug "{%s}" str

let dump_expr e =
  let ctx = get_ctx () in
  let string_of_type tp = PrettyPrinter.pp_type ~ctx @@ Schema.get_template tp in
  let str = Core.Imast.string_of_expr e VarTbl.find string_of_type in
  debug "%s" str

let dump_expr' e =
  let string_of_type = Imast.pp_expl_type VarTbl.find in
  let str = Core.Imast.string_of_expr e VarTbl.find string_of_type in
  debug "%s" str

let dump_uvar_set x tp =
  let ctx = get_ctx () in
  let uvar_str = PrettyPrinter.pp_lookup_uvar ~ctx x in
  let tp_str   = PrettyPrinter.pp_type ~ctx tp in
  debug "  [%s <-  %s]" uvar_str tp_str

let dump_var ?(register=true) (x,typ) =
  if register then register_var (x,typ);
  debug "[%s : %s]" (VarTbl.find x) (pp_typ typ)


let counter = ref 0
let mark fmt =
  let f str =
    debug "[%d] %s" !counter str;
    incr counter
  in Printf.ksprintf f fmt

(* ========================================================================= *)

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
    Utils.report_error node "Undefined variable: %s in %s" name str

let report_level_difference (node : 'a Imast.expr) adt adtlvl uvarlvl =
  Utils.report_error node
      "Levels difference [%s>>%s]: %s escapes scope."
      (Type.Level.to_string adtlvl)
      (Type.Level.to_string uvarlvl)
      (VarTbl.find adt)

let report_cannot_unify (node : 'a Imast.expr) expected actual =
  let open PrettyPrinter in
  Utils.report_error node
    "Expression has type %s,\nbut was expected to be of type %s."
    (pp_type actual) (pp_type expected)
