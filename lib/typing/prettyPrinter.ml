open Type
module Utils = Core.Utils

(* ========================================================================== *)
(* Pretty printing of types *)

type ('a, 'b, 'c) vars =
  | AnonVar of 'a
  | NamedVar of 'c
  | UVar of 'b

type ('a, 'b, 'c) ctx_struct = {
  env:   (('a, 'b, 'c) vars * string) list;
  uvars: int;
  anons: int;
  named: int;
}

(* ========================================================================== *)
(** Creates fresh pretty-printing context *)
let pp_context () =
  let var_seq = Core.Imast.VarTbl.to_seq () in
  ref {
    env=List.of_seq var_seq |> List.map (fun (k, v) -> (NamedVar k, v));
    uvars=0; anons=0; named=0; }

let pp_at_level l lvl str =
  if lvl > l then Printf.sprintf "(%s)" str
  else str

let cmp x y =
  match x, y with
  | NamedVar x, NamedVar y -> Core.Imast.IMAstVar.compare x y = 0
  | AnonVar x,  AnonVar y -> TVar.compare x y = 0
  | UVar x, UVar y -> Type.uvar_compare x y = 0
  | _ -> false

let rec assq_opt x = function
  | (y, v) :: _ when cmp x y -> Some v
  | _ :: xs -> assq_opt x xs
  | [] -> None

let pp_context_lookup x ctx =
  let { env; uvars; anons; named; } = !ctx in
  match x, assq_opt x env with
    | _, Some str -> str
    | NamedVar _, None ->
      (* this shouldn't happen, internal error *)
      let name = "#" ^ Utils.type_name_gen named in
      ctx := { !ctx with env=(x, name) :: env; named=named+1 };
      name
    | AnonVar _, None ->
      let name = "'" ^ Utils.type_name_gen anons in
      ctx := { !ctx with env=(x, name) :: env; anons=anons+1 };
      name
    | UVar uv, None ->
      let name = "?" ^ Type.string_of_uvar uv ^ Utils.type_name_gen uvars in
      ctx := { !ctx with env=(x, name) :: env; uvars=uvars+1 };
      name


let rec pp_type ctx lvl tp =
  let rec matcher lvl = function
    | TVar x -> pp_context_lookup (AnonVar x) ctx
    | TADT (x, _, tps) -> 
      let x = pp_context_lookup (NamedVar x) ctx in
      let tps = pp_list "," ctx 1 tps |> pp_at_level 1 (List.length tps) in
      pp_at_level 0 lvl
        (Printf.sprintf "%s %s" x tps)
    | TUnit  -> "Unit"
    | TEmpty -> "Empty"
    | TBool  -> "Bool"
    | TInt   -> "Int"
    | TUVar x -> pp_context_lookup (UVar x) ctx
    | TArrow(targ, tres) ->
      pp_at_level 0 lvl
        (Printf.sprintf "%s -> %s" (pp_type ctx 0 targ) (pp_type ctx 0 tres))
    | TPair(tp1, tp2) ->
      pp_at_level 2 lvl
        (Printf.sprintf "%s * %s"
          (pp_type ctx 3 tp1)
          (pp_type ctx 3 tp2))
  and pp_list separator ctx lvl = function
    | [ tp ] -> pp_type ctx (lvl-1) tp
    | tp :: tps ->
        Printf.sprintf "%s %s %s" (pp_type ctx lvl tp) separator (pp_list separator ctx lvl tps)
    | [] -> "Unit"
  in Type.view tp |> matcher lvl

let pp_type = pp_type (pp_context ()) 0

(* ========================================================================== *)
(** PrettyPrint expression *)

let pp_expr e =
  let ctx = pp_context () in
  let string_of_var x = pp_context_lookup (NamedVar x) ctx in
  let string_of_type tp = pp_type @@ Schema.get_template tp in
  Core.Imast.string_of_expr e string_of_var string_of_type


let pp_ctx () =
  let open Core.Imast in
  let { env; uvars; anons; named; } = !(pp_context ()) in
  let f (var, str) =
    (match var with
      | NamedVar x -> Printf.sprintf "%s : %s" (IMAstVar.to_string x) str
      | AnonVar x -> Printf.sprintf "'%s : %s" (TVar.to_string x) str
      | UVar uv -> Printf.sprintf "?%s : %s" (Type.string_of_uvar uv) str
    ) |> fun str -> "("^str^")"
  in
  List.map f env
  |> String.concat " "
  |> fun str -> "["^str^"]"
