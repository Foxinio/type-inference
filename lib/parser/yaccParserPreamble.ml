open Core
open Ast

type 'typ def =
| DLet of 'typ var * 'typ expr
| DType of alias * (ctor_name * 'typ) list
| DTypeAlias of alias * 'typ

let make data =
  { data      = data;
    typ       = THole;
    start_pos = Parsing.symbol_start_pos ();
    end_pos   = Parsing.symbol_end_pos ();
  }

let make_with_typ data typ =
  { (make data) with typ=typ }

let extract args typ =
  let extract_ids arg = (arg.data, arg.typ) in
  let found = ref (typ = THole) in
  let extract_typ = function
    | {typ=THole; _}   -> THole
    | {typ=tp;_} -> found := true; tp
  in
  let extracted_typ = List.map extract_typ args in
  (List.map extract_ids args,
   if !found then
    TArrow (Pure, extracted_typ, typ)
    else THole)

let desugar_fn args body typ =
  let args, typ = extract args typ in
  { (make (EFn(args, body))) with typ }

let desugar_fix fn args body typ =
  let args, typ = extract args typ in
  { (make (EFix((fn, typ), args, body))) with typ }

let desugar_let_fun f args body typ =
  let args, typ = extract args typ in
  let fn = { (make (EFn(args, body))) with typ } in
  make (DLet((f,typ), fn))

let desugar_let_rec fn args body typ =
  let args, typ = extract args typ in
  let fix = { (make (EFix((fn, typ), args, body))) with typ } in
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

let desugar_app = function
  | fn :: args ->
    make (EApp(fn, args))
  | [] -> assert false

(* maybe there is a better way to do this,
   but i think its over all a good idea *)
let desugar_type_alias id args =
  if id = "_" then begin
    assert(List.length args = 0);
    THole
  end else TAlias (id, args)


