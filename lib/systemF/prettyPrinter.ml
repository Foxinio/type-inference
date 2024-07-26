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

let pp_context () = ref {env=[]; anons=0; named=0; }

let pp_context_of_seq var_seq = 
  ref {
    env=List.of_seq var_seq |> List.map (fun (k, v) -> (NamedVar k, v));
    anons=0;
    named=0;
  }

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
      let name = "#" ^ Utils.type_name_gen named in
        ctx := { !ctx with env=(x, name) :: env; named=named+1 };
        name
    | AnonVar _, None ->
      let name = "'" ^ Utils.type_name_gen anons in
      ctx := { !ctx with env=(x, name) :: env; anons=anons+1 };
      name

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
    let tps = pp_list "," ctx 1 tps |> pp_at_level 1 (List.length tps) in
    pp_at_level 0 lvl
      (sprintf "%s %s" x tps)
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

let string_of_type = pp_type (pp_context ())

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
    | _, _ -> failwith "impossible"
  in match xs, tp with
    | _ :: xs, TArrow(arr, _, tres) -> inner arr (xs, tres)
    | _ -> failwith "impossible"

let rec pp_expr (indent : string) ctx (lvl : int) : expr -> string = function
  | EUnit -> "()"
  | EBool b when b -> "true"
  | EBool _ -> "false"
  | ENum n ->
    let str = string_of_int n in
    str
  | EVar x ->
    let name = pp_context_lookup (NamedVar x) ctx in
    name

  | EFn (xs, body, tp) ->
    let vars, tres = pp_fn_args ctx xs tp in
    let tstr = pp_type ctx tres in
    let purity = get_purity xs tp in
    let body_str = pp_expr (indent^"  ") ctx fun_lvl body in
    pp_at_level fun_lvl lvl
      (sprintf "fun %s : %s ->%s%s"
        (String.concat " " vars)
        tstr
        purity
        (endline' indent body_str))

  | EFix (f, xs, body, tp) ->
    let vars, tres = pp_fn_args ctx xs tp in
    let tstr = pp_type ctx tres in
    let body_str = pp_expr (indent^"  ") ctx fun_lvl body in
    pp_at_level fun_lvl lvl
      (sprintf "fix %s %s : %s ->%s"
        (pp_context_lookup (NamedVar f) ctx)
        (String.concat " " vars)
        tstr @@ endline' indent body_str)

  | EApp(e1, es) ->
    let e1str = pp_expr (indent^"  ") ctx app_lvl e1 in
    let estr = pp_list (indent^"  ") ctx app_lvl es in
    pp_at_level (app_lvl-1) lvl
      (sprintf "%s %s" e1str estr)

  | ETFn (xs, body) ->
    let bodystr = pp_expr (indent^"  ") ctx (lvl+1) body in
    let xs = List.map (fun x -> pp_context_lookup (AnonVar x) ctx) xs in
    pp_at_level fun_lvl lvl
      (sprintf "Λ %s. %s" (String.concat " " xs) @@ endline' indent bodystr)

  | ETApp (e, tps) ->
    let e1str = pp_expr (indent^"  ") ctx tapp_lvl e in
    let tpstrs = List.map (pp_type ctx) tps in
    let tpstr = sprintf "[%s]" (String.concat ", " tpstrs) in
    pp_at_level tapp_lvl lvl
      (sprintf "%s %s" e1str tpstr)
  | ELet (f, EFn(xs, body, tp), e2) ->
    let body = pp_expr (indent^"  ") ctx def_lvl body in
    let e2 = pp_expr (indent^"  ") ctx def_lvl e2 in
    let vars, tres = pp_fn_args ctx xs tp in
    pp_at_level def_lvl lvl
      (sprintf "let %s %s : %s =%s%s%s"
        (pp_context_lookup (NamedVar f) ctx)
        (String.concat " " vars)
        (pp_type ctx tres)
        (endline' indent body)
        (endline indent "in")
        (endline indent e2))

  | ELet (f, EFix(_, xs, body, tp), e2) ->
    let body = pp_expr (indent^"  ") ctx def_lvl body in
    let e2 = pp_expr (indent^"  ") ctx def_lvl e2 in
    let vars, tres = pp_fn_args ctx xs tp in
    pp_at_level def_lvl lvl
      (sprintf "let rec %s %s : %s =%s%s%s"
        (pp_context_lookup (NamedVar f) ctx)
        (String.concat " " vars)
        (pp_type ctx tres)
        (endline' indent body)
        (endline indent "in")
        (endline indent e2))

  | ELet (x, e1, e2) ->
    let e1' = pp_expr (indent^"  ") ctx def_lvl e1 in
    let e2 = pp_expr indent ctx def_lvl e2 in
    pp_at_level def_lvl lvl
      (sprintf "let %s =%s%s%s"
        (pp_context_lookup (NamedVar x) ctx)
        (endline' indent e1')
        (endline indent "in")
        (endline indent e2))

  | EExtern (name, tp) ->
    sprintf "(%s : %s)" name (pp_type ctx tp)

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
    let bodystr = pp_expr (indent^"  ") ctx def_lvl body in
    let alias'  = pp_context_lookup (NamedVar alias) ctx in
    let argsstr =
      let str = List.map (fun x -> pp_context_lookup (AnonVar x) ctx) args in
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

  | ECtor (name, body) ->
    let bodystr = pp_expr (indent^"  ") ctx app_lvl body in
    let name' = pp_context_lookup (NamedVar name) ctx in
    pp_at_level app_lvl lvl
      (sprintf "%s %s" name' bodystr)

  | EMatch (body, clauses, _) ->
    let bodystr = pp_expr (indent^"  ") ctx app_lvl body in
    let clausesstr = pp_clauses (indent^"  ") ctx clauses in
    pp_at_level app_lvl lvl
      (sprintf "match %s with%s%s" bodystr clausesstr @@ endline indent "end")

and pp_fn_args ctx xs tp : string list * tp =
  let rec inner acc = function
    | x :: xs, TArrow(_, targ, tres) ->
      let name = pp_context_lookup (NamedVar x) ctx in
      let tstr = pp_type ctx targ in
      let str = sprintf "(%s : %s)" name tstr in
      inner (str::acc) (xs,tres)
    | [], tp ->
      List.rev acc, tp
    | _::_, _ -> failwith "internal error"
  in inner [] (xs, tp)

and pp_list indent ctx lvl lst =
  let estrs = List.map (pp_expr (indent^"  ") ctx (lvl+1)) lst in
  let sep = "\n"^indent in
  String.concat sep estrs |> endline indent

and pp_ctors indent ctx ctors =
  let f (name, tp) =
    let tstr = pp_type ctx tp in
    let name = pp_context_lookup (NamedVar name) ctx in
    sprintf "%s| %s of %s" indent name tstr
  in
  let estrs = List.map f ctors in
  let sep = "\n" in
  String.concat sep estrs |> endline indent

and pp_clauses indent ctx clauses =
  let f (ctor, var, body) =
    let ctor_name = pp_context_lookup (NamedVar ctor) ctx in
    let var_name = pp_context_lookup (NamedVar var) ctx in
    let bodystr = pp_expr (indent^"  ") ctx app_lvl body in
    sprintf "%s| %s %s ->%s" indent ctor_name var_name @@ endline' indent bodystr
  in
  let estrs = List.map f clauses in
  let sep = "\n" in
  String.concat sep estrs |> endline indent

let pp_expr ctx = pp_expr "" ctx 0
