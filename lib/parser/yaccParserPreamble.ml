open Core
open Ast

type 'typ def =
  | DLet of 'typ var_def * 'typ expr
  | DType of alias * (ctor_name * 'typ) list
  | DTypeAlias of alias * 'typ

let make data =
    let res = { data;
        typ       = THole;
        start_pos = Parsing.symbol_start_pos ();
        end_pos   = Parsing.symbol_end_pos ();
      } in
    res

let make_with_typ data typ =
  { (make data) with typ=typ }

(* given arguments (wrapped in node) and type this arrow returns,
   gives arguments ids (as pairs) and type of a whole arrow
    (if no argument was annotated with a type, second result is a THole *)
let extract args typ =
  let extract_ids arg = (arg.data, arg.typ) in
  let found = ref (typ <> THole) in
  let extract_typ = function
    | {typ=THole; _}   -> THole
    | {typ=tp;_} -> found := true; tp
  in
  let extracted_typ = List.map extract_typ args in
  List.map extract_ids args,
  if !found then t_arrow extracted_typ typ else THole

let fold_fn args body typ =
  let aux arg body =
    { (make (EFn (arg, body))) with typ=THole }
  in
  { (List.fold_right aux args body) with typ }

let desugar_fn args body typ =
  let args, typ = extract args typ in
  fold_fn args body typ

let fold_fix fn args body typ =
  match args with
  | arg :: args ->
    let body = fold_fn args body typ in
    { (make (EFix((fn, typ), arg, body))) with typ }
  | [] -> assert false

let desugar_fix fn args body typ =
  let args, typ = extract args typ in
  fold_fix fn args body typ

let desugar_let_fun f args body typ =
  let args, typ = extract args typ in
  let fn = fold_fn args body typ in
  make (DLet((f,typ), fn))

let desugar_let_rec fn args body typ =
  let args, typ = extract args typ in
  let fix = fold_fix fn args body typ in
  make (DLet((fn, typ), fix))

let desugar_def def rest =
  match def.data with
  | DLet(x, body) ->
    { data      = ELet(x, body, rest);
      typ       = THole;
      start_pos = def.start_pos;
      end_pos   = rest.end_pos
    }
  | DType(x, cts) ->
    { data      = EType(x, cts, rest);
      typ       = THole;
      start_pos = def.start_pos;
      end_pos   = rest.end_pos
    }
  | DTypeAlias(vars, name) ->
    { data      = ETypeAlias(vars, name, rest);
      typ       = THole;
      start_pos = def.start_pos;
      end_pos   = rest.end_pos
    }

let desugar_defs defs rest =
  List.fold_right desugar_def defs rest

(* maybe there is a better way to do this,
   but i think its over all a good idea *)
let desugar_type_alias id args =
  if id = "_" then begin
    assert(List.length args = 0);
    THole
  end else TAlias (id, args)


(* ######################################################################### *)
(* TESTS *)

let%test_module "LmParser.YaccParserPreambule Testing module" =
  (module struct

  let cmp (a,_) b = String.equal a b
  let corr_args = ["x1"; "x2"; "x3"]
  let args = List.map make corr_args
  let typ  = THole
  let body = make EUnit
  let print_expl tp = pp_expl_type Fun.id tp |> prerr_endline

  let%test "extract test typ=THole" =
    let args', typ' = extract args typ in
    List.for_all2 cmp args' corr_args && typ' = THole

(* ------------------------------------------------------------------------- *)

  let unfold_fn e =
    let rec inner acc tres = function
    | EFn(arg, body) -> inner (arg::acc) body.typ body.data
    | _ -> List.rev acc, body, tres
    in match e.data with
    | EFn(arg, body) -> inner [arg] body.typ body.data, e.typ
    | _ -> raise (Invalid_argument "unfold_fn expects an arrow")

  let%test "fold_fn test: simple" =
    let fn = desugar_fn args body typ in
    let (args', body', tres'), typ' = unfold_fn fn in
    List.for_all2 cmp args' corr_args
    && typ' = typ
    && body' = body
    && tres' = THole

  let%test "fold_fn test: one annotated arg" =
    let x' = "x'" in
    let corr_typ = TArrow(TUnit, TArrow(THole, TArrow(THole, TArrow(THole, THole)))) in
    let fn = desugar_fn (make_with_typ x' TUnit :: args) body typ in
    let (args', body', tres), typ' = unfold_fn fn in
    List.for_all2 cmp args' (x'::corr_args)
    && typ' = corr_typ
    && body' = body
    && tres = THole

(* ------------------------------------------------------------------------- *)

  let unfold_fix e =
    let rec inner acc = function
    | EFn(arg, body) -> inner (arg::acc) body.data
    | _ -> List.rev acc, body
    in match e.data with
    | EFix((_,typ), arg, body) -> inner [arg] body.data, e.typ, typ
    | _ -> raise (Invalid_argument "unfold_fn expects an arrow")

  let%test "fold_fix test: one annotated arg" =
    let x' = "x'" in
    let corr_typ = TArrow(TUnit, TArrow(THole, TArrow(THole, TArrow(THole, THole)))) in
    let fn = desugar_fix "" (make_with_typ x' TUnit :: args) body typ in
    let (args', body'), typ', ftyp = unfold_fix fn in
    assert (List.for_all2 cmp args' (x'::corr_args));
    assert (typ' = corr_typ);
    assert (body' = body);
    assert (typ' = ftyp);
    true

  let%test "fold_fix test: annotated result" =
    let corr_typ = TArrow(THole, TArrow(THole, TArrow(THole, TInt))) in
    let fn = desugar_fix "" args body TInt in
    let (args', body'), typ', ftyp = unfold_fix fn in
    assert (List.for_all2 cmp args' corr_args);
    assert (typ' = corr_typ);
    assert (body' = body);
    assert (typ' = ftyp);
    true

end)
