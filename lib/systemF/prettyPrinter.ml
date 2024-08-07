open Main
open Printf

module Utils = Core.Utils

(* ========================================================================= *)
(* Pretty printing of types *)

type ('a, 'c) vars =
  | AnonVar of 'a
  | NamedVar of 'c

type ('a, 'c) ctx_struct = {
  env:   (('a, 'c) vars * string) list;
  anons: int;
  named : int;
}

type ('a, 'c) ctx = ('a, 'c) ctx_struct ref

(* ========================================================================= *)
(** Creates fresh pretty-printing context *)

let ctx = ref None

let create_context () =
  let var_seq = Core.Imast.VarTbl.to_seq () in
  ref {
    env=List.of_seq var_seq |> List.map (fun (k, v) -> (NamedVar k, v));
    anons=0;
    named=0;
  }

let pp_context () =
  match !ctx with
  | None ->
    let ctx' = create_context () in
    ctx := Some ctx';
    ctx'
  | Some ctx' -> ctx'

let pp_at_level l lvl str =
  if lvl > l then sprintf "(%s)" str
  else str

let cmp x y =
  match x, y with
  | NamedVar x, NamedVar y -> Core.Imast.IMAstVar.compare x y = 0
  | AnonVar x,  AnonVar y -> TVar.compare x y = 0
  | _ -> false

let rec assq_opt x = function
  | (y, v) :: _ when cmp x y -> Some v
  | _ :: xs -> assq_opt x xs
  | [] -> None

let pp_context_lookup x ctx =
  let { env; anons; named } = !ctx in
  match x, assq_opt x env with
    | _, Some str -> str
    | NamedVar y, None ->
      (* this shouldn't happen, internal error *)
      let name = "#" ^ Utils.gen_name named in
        ctx := { !ctx with env=(x, name) :: env; named=named+1 };
        name
    | AnonVar _, None ->
      let name = "'" ^ Utils.gen_name anons in
      ctx := { !ctx with env=(x, name) :: env; anons=anons+1 };
      name

let pp_lookup_var ?(ctx=pp_context ()) x =
  pp_context_lookup (NamedVar x) ctx

let pp_lookup_tvar ?(ctx=pp_context ()) x =
  pp_context_lookup (AnonVar x) ctx

let arr_str arr =
  match Arrow.view arr with
  | EffPure, FldUnfolded   -> "->p"
  | EffPure, FldFolded     -> ","
  | EffImpure, FldUnfolded -> "->i"
  | EffImpure, FldFolded   -> ",'"

let rec pp_type ctx lvl = function
  | TVar x -> pp_context_lookup (AnonVar x) ctx
  | TADT (x, tps) -> 
    let x = pp_context_lookup (NamedVar x) ctx in
    let tps' = pp_list "," ctx 1 tps |> pp_at_level 1 (List.length tps) in
    let str =
      if List.is_empty tps then x
      else if List.length tps = 1 then sprintf "%s %s" x tps'
      else sprintf "%s (%s)" x tps'
    in
    pp_at_level 0 lvl str
  | TUnit  -> "Unit"
  | TEmpty -> "Empty"
  | TBool  -> "Bool"
  | TInt   -> "Int"
  | TArrow(arr, targ, tres) ->
      let arr_str = arr_str arr in
      pp_at_level 0 lvl
        (sprintf "%s %s %s"
          (pp_type ctx 1 targ)
          arr_str
          (pp_type ctx 0 tres))
  | TPair(tp1, tp2) ->
    pp_at_level 2 lvl
      (sprintf "%s * %s"
        (pp_type ctx 3 tp1)
        (pp_type ctx 3 tp2))
  | TForallT (tvars, tp) -> 
    let tvars = List.map (fun v -> pp_context_lookup (AnonVar v) ctx) tvars in
    pp_at_level 3 lvl
      (sprintf "∀ %s. %s" (String.concat "," tvars) (pp_type ctx 0 tp))

and pp_list separator ctx lvl tps =
  String.concat separator @@ List.map (pp_type ctx lvl) tps

let pp_type ctx = pp_type ctx 0

(* ========================================================================= *)

let endline indent str =
  sprintf "\n%s%s" indent str

let endline' indent str =
  sprintf "\n  %s%s" indent str

let fun_lvl = 0
let tapp_lvl = 1
let app_lvl = 2
let def_lvl = 3
let pair_lvl = 4
let if_lvl = 5
let seq_lvl = 6
let match_lvl = 7

let get_purity xs tp =
  let rec inner arr = function
    | _::xs, TArrow(_, _, tres) ->
      inner arr (xs, tres)
    | [], _ ->
      if Arrow.view_eff arr = EffPure
      then "p"
      else "i"
    | _, _ -> failwith "internal error: expected TArrow"
  in match xs, tp with
    | _ :: xs, TArrow(arr, _, tres) -> inner arr (xs, tres)
    | [], _ -> failwith "internal error: empty list of arguments"
    | _, _  -> failwith "internal error: expected TArrow"

let pp_type' ctx = pp_type (fst ctx)
let pp_lookup_tvar' ctx = pp_lookup_tvar ~ctx:(fst ctx)
let pp_lookup_var' ctx = pp_lookup_var ~ctx:(fst ctx)
let pp_lookup_tp' ctx x = Utils2.Env.lookup_var (snd ctx) x
let pp_var' ctx x = sprintf "%s : %s"
  (pp_lookup_var' ctx x) (pp_lookup_tp' ctx x |> pp_type' ctx)

module Env = struct
  type t = (tvar, var) ctx_struct ref * Utils2.Env.t

  let extend_vars ctx xs tp =
    Utils2.Env.extend_var (snd ctx) xs tp
    |> fun (tp, env, eff) -> tp, (fst ctx, env)

  let extend_ctors ctx ctor_lst alias_name targs =
    fst ctx, Utils2.Env.extend_ctors (snd ctx) ctor_lst alias_name targs

  let add_var ctx x tp =
    fst ctx, Utils2.Env.add_var (snd ctx) x tp

  let lookup_var ctx x = Utils2.Env.lookup_var (snd ctx) x

  let lookup_ctor ctx ctor = Utils2.Env.lookup_ctor (snd ctx) ctor

  let extend_clause ctx var ctor args =
    let expected, alias', tvars = lookup_ctor ctx ctor in
    let substituted = Subst.subst_list expected tvars args in
    add_var ctx var substituted

end

let infer ctx e = Utils2.infer_type (snd ctx) e |> fst

let rec pp_expr (indent : string) (ctx : Env.t) (lvl : int) : expr -> string = function
  | EUnit -> "()"
  | EBool b -> string_of_bool b
  | ENum n -> string_of_int n
  | EVar x -> pp_lookup_var' ctx x

  | EFn (xs, body, tp) ->
    let vars, ctx', tres = pp_fn_args ctx xs tp in
    let tstr = pp_type' ctx' tres in
    assert(not @@ List.is_empty xs);
    let purity = get_purity xs tp in
    let body_str = pp_expr (indent^"  ") ctx' fun_lvl body in
    pp_at_level fun_lvl lvl
      (sprintf "fun %s : %s =>%s%s"
        (String.concat " " vars)
        tstr
        purity
        (endline' indent body_str))

  | EFix (f, xs, body, tp) ->
    let vars, ctx', tres = pp_fn_args ctx xs tp in
    let ctx' = Env.add_var ctx' f tp in
    let tstr = pp_type' ctx' tres in
    let body_str = pp_expr (indent^"  ") ctx' fun_lvl body in
    pp_at_level fun_lvl lvl
      (sprintf "fix %s %s : %s =>i%s"
        (pp_lookup_var' ctx' f)
        (String.concat " " vars)
        tstr @@ endline' indent body_str)

  | EApp(e1, es) ->
    pp_app indent ctx lvl e1 es

  | ETFn (xs, body) ->
    let bodystr = pp_expr (indent^"  ") ctx (lvl+1) body in
    let xs = List.map (fun x -> pp_lookup_tvar' ctx x) xs in
    pp_at_level fun_lvl lvl
      (sprintf "Λ %s. %s" (String.concat " " xs) @@ endline' indent bodystr)

  | ETApp (e, tps) ->
    let e1str = pp_expr (indent^"  ") ctx tapp_lvl e in
    let tpstrs = List.map (pp_type' ctx) tps in
    let tpstr = sprintf "[%s]" (String.concat ", " tpstrs) in
    pp_at_level tapp_lvl lvl
      (sprintf "%s %s" e1str tpstr)

  | ELet (x, e1, e2) ->
    let e1' = pp_expr (indent^"  ") ctx def_lvl e1 in
    let tp1 = infer ctx e1 in
    let ctx' = Env.add_var ctx x tp1 in
    let e2 = pp_expr indent ctx' def_lvl e2 in
    pp_at_level def_lvl lvl
      (sprintf "let %s : %s =%s%s%s"
        (pp_lookup_var' ctx' x)
        (pp_type' ctx' tp1)
        (endline' indent e1')
        (endline indent "in")
        (endline indent e2))

  | EExtern (name, tp) ->
    sprintf "(%s : %s)" name (pp_type' ctx tp)

  | EPair(e1, e2) ->
    let e1str = pp_expr (indent^"  ") ctx pair_lvl e1 in
    let e2str = pp_expr (indent^"  ") ctx pair_lvl e2 in
    pp_at_level pair_lvl lvl
      (sprintf "%s, %s" e1str e2str)

  | EFst e ->
    let e1str = pp_expr (indent^"  ") ctx app_lvl e in
    pp_at_level app_lvl lvl
      (sprintf "fst %s" e1str)

  | ESnd e ->
    let e1str = pp_expr (indent^"  ") ctx app_lvl e in
    pp_at_level app_lvl lvl
      (sprintf "snd %s" e1str)

  | EIf (cond, e1, e2) ->
    let condstr = pp_expr (indent^"  ") ctx if_lvl cond in
    let e1str = pp_expr (indent^"  ") ctx if_lvl e1 in
    let e2str = pp_expr (indent^"  ") ctx if_lvl e2 in
    pp_at_level if_lvl lvl
      (sprintf "if %s%s%s"
        condstr
        (endline indent @@ sprintf "then %s" e1str)
        (endline indent @@ sprintf "else %s" e2str))

  | ESeq (e1, e2) ->
    let e1str = pp_expr (indent^"  ") ctx seq_lvl e1 in
    let e2str = pp_expr (indent^"  ") ctx seq_lvl e2 in
    pp_at_level seq_lvl lvl
      (sprintf "%s;%s" e1str @@ endline indent e2str)

  | EType (alias, args, ctors, body) ->
    let ctx = Env.extend_ctors ctx ctors alias args in
    let bodystr = pp_expr indent ctx def_lvl body in
    let alias'  = pp_lookup_var' ctx alias in
    let argsstr =
      let str = List.map (fun x -> pp_lookup_tvar' ctx x) args in
      if List.length str = 0 then ""
      else if List.length str = 1 then " " ^ List.hd str
      else " (" ^ String.concat ", " str ^ ")"
    in
    pp_at_level def_lvl lvl
      (sprintf "type %s%s =%s%s%s"
        alias' argsstr
        (pp_ctors (indent^"  ") ctx ctors)
        (endline indent "in")
        (endline' indent bodystr))

  | ECtor (name, adt_args, body) ->
    let bodystr = pp_expr (indent^"  ") ctx app_lvl body in
    let adt_args' = List.map (pp_type' ctx) adt_args
      |> String.concat ", " in
    let name' = pp_lookup_var' ctx name in
    pp_at_level app_lvl lvl
      (sprintf "%s [%s] (%s)" name' adt_args' bodystr)

  | EMatch (body, clauses, _) ->
    let bodystr = pp_expr (indent^"  ") ctx app_lvl body in
    let body_tp = infer ctx body in
    let clausesstr = pp_clauses (indent^"  ") ctx clauses body_tp in
    pp_at_level app_lvl lvl
      (sprintf "match %s with%s%s" bodystr clausesstr @@ endline indent "end")

and pp_fn_args ctx xs tp : string list * ((tvar, var) ctx_struct ref * Utils2.Env.t) * tp =
  let rec inner acc ctx = function
    | x :: xs, TArrow(_, targ, tres) ->
      let name = pp_lookup_var' ctx x in
      let tstr = pp_type' ctx targ in
      let ctx = Env.add_var ctx x targ in
      let str = sprintf "(%s : %s)" name tstr in
      inner (str::acc) ctx (xs,tres)
    | [], tp ->
      List.rev acc, ctx, tp
    | _::_, _ -> failwith "internal error"
  in inner [] ctx (xs, tp)

and pp_app indent ctx lvl e1 es =
  let e1str = pp_expr (indent^"  ") ctx app_lvl e1 in
  let tp1 = infer ctx e1 in
  let estr = pp_args (indent^"  ") ctx app_lvl es tp1 in
  pp_at_level (app_lvl-1) lvl
    (sprintf "%s : %s%s" e1str (pp_type' ctx tp1) @@ endline indent estr)

and pp_args indent ctx lvl lst tp1 =
  let rec inner acc = function
    | e :: es, TArrow(_, targ, tres) ->
      let estr = pp_expr (indent^"  ") ctx (lvl+1) e in
      let tp   = infer ctx e in
      let str = if Order.type_equal tp targ
        then sprintf "(%s : %s)" estr @@ pp_type' ctx tp
        else sprintf "(%s : [%s <: %s])" estr (pp_type' ctx tp) (pp_type' ctx targ)
      in
      inner (str :: acc) (es, tres)
    | [], tp -> List.rev acc
    | _::_,_ -> failwith "internal error"
  in
  let estrs = inner [] (lst, tp1) in
  let sep = "\n"^indent in
  String.concat sep estrs

and pp_ctors indent ctx ctors =
  let f (name, tp) =
    let tstr = pp_type' ctx tp in
    let name = pp_lookup_var' ctx name in
    sprintf "| %s of %s" name tstr
  in
  let estrs = List.map f ctors in
  let sep = "\n"^indent in
  String.concat sep estrs |> endline indent

and pp_clauses indent ctx clauses body_tp =
  let[@warning "-8"] TADT(alias,args) = body_tp in
  let f (ctor, var, body) =
    let ctx = Env.extend_clause ctx var ctor args in
    let ctor_name = pp_lookup_var' ctx ctor in
    let var_name = pp_var' ctx var in
    let bodystr = pp_expr (indent^"  ") ctx app_lvl body in
    sprintf "| %s %s =>%s" ctor_name var_name @@ endline' indent bodystr
  in
  let estrs = List.map f clauses in
  let sep = "\n"^indent in
  String.concat sep estrs |> endline indent

let pp_expr ?(ctx=pp_context ()) (env : Utils2.Env.t) e =
  pp_expr "" (ctx, env) 0 e

let pp_type ?(ctx=pp_context ()) = pp_type ctx

let pp_ctx () =
  let open Core.Imast in
  let { env; anons; named; } = !(pp_context ()) in
  let f (var, str) =
    (match var with
      | NamedVar x -> Printf.sprintf "%s : %s" (IMAstVar.to_string x) str
      | AnonVar x -> Printf.sprintf "'%s : %s" (TVar.to_string x) str
    ) |> fun str -> "("^str^")"
  in
  List.map f env
  |> String.concat " "
  |> fun str -> "["^str^"]"
