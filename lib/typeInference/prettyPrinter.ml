open Type

(* ========================================================================= *)
(* Pretty printing of types *)

type ('a, 'b) vars =
  | AnonVar of 'a
  | UVar of 'b

type ('a, 'b) ctx = {
  env:   (('a, 'b) vars * string) list;
  uvars: int;
  anons: int
}

let type_name_gen i =
  let limit = (Char.code 'z') - (Char.code 'a') + 1 in
  let rec inner i =
    if i >= 0 && i < limit then Char.chr i |> String.make 1 
    else
      let minor = i mod limit |> inner
      and major = i / limit |> inner in
      major ^ minor
  in
  inner i

(** Creates fresh pretty-printing context *)
let pp_context () = ref {env=[]; uvars=0; anons=0}

let pp_context_of_seq var_seq = 
  ref {
    env=List.of_seq var_seq |> List.map (fun (k, v) -> (AnonVar k, v));
    uvars=0; anons=0}

let pp_at_level l lvl str =
  if lvl > l then Printf.sprintf "(%s)" str
  else str

let pp_context_lookup x ctx =
  let { env; uvars; anons } = !ctx in
  match x, List.assq_opt x env with
    | _, Some str -> str
    | AnonVar _, None ->
      let name = "'" ^ type_name_gen anons in
      ctx := { env=(x, name) :: env; uvars; anons=anons+1 };
      name
    | UVar _, None ->
      let name = "?" ^ type_name_gen uvars in
      ctx := { env=(x, name) :: env; uvars=uvars+1; anons };
      name


let rec pp_type ctx lvl tp =
  let rec matcher lvl = function
    | TVar x -> pp_context_lookup (AnonVar x) ctx
    | TADT (x, tps) -> 
      let x = pp_context_lookup (AnonVar x) ctx in
      let tps = pp_list "," ctx 1 tps |> pp_at_level 1 (List.length tps) in
      pp_at_level 0 lvl
        (Printf.sprintf "%s %s" x tps)
    | TUnit  -> "Unit"
    | TEmpty -> "Empty"
    | TBool  -> "Bool"
    | TInt   -> "Int"
    | TUVar x -> pp_context_lookup (UVar x) ctx
    | TGVar (x, None) -> pp_context_lookup (UVar x) ctx
    | TGVar (x, Some tp) ->
        matcher lvl tp
    | TArrow(tps, tp2) ->
      pp_at_level 0 lvl
        (Printf.sprintf "%s -> %s" (pp_list "," ctx 1 tps) (pp_type ctx 0 tp2))
    | TProd(tps) ->
      pp_at_level 2 lvl
        (Printf.sprintf "%s" (pp_list "*" ctx 3 tps))
    and pp_list separator ctx lvl = function
    | [ tp ] -> pp_type ctx (lvl-1) tp
    | tp :: tps ->
        Printf.sprintf "%s %s %s" (pp_type ctx lvl tp) separator (pp_list separator ctx lvl tps)
    | [] -> "Unit"
  in Type.view tp |> matcher lvl

let string_of_type = pp_type (pp_context ()) 0
