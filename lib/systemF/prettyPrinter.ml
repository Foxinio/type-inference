open Type

(* ========================================================================== *)
(* Pretty printing of types *)

type ('a, 'c) vars =
  | AnonVar of 'a
  | NamedVar of 'c

type ('a, 'c) ctx_struct = {
  env:   (('a, 'c) vars * string) list;
  anons: int
}

type ('a, 'c) ctx = ('a, 'c) ctx_struct ref

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

(* ========================================================================== *)
(** Creates fresh pretty-printing context *)

let pp_context () = ref {env=[]; anons=0}

let pp_context_of_seq var_seq = 
  ref {
    env=List.of_seq var_seq |> List.map (fun (k, v) -> (NamedVar k, v));
    anons=0}

let pp_at_level l lvl str =
  if lvl > l then Printf.sprintf "(%s)" str
  else str

let pp_context_lookup x ctx =
  let { env; anons } = !ctx in
  match x, List.assq_opt x env with
    | _, Some str -> str
    | NamedVar x, None ->
      (* this shouldn't happen, internal error *)
      Core.Utils.report_internal_error "Named variable not found by pretty printer"
    | AnonVar _, None ->
      let name = "'" ^ type_name_gen anons in
      ctx := { env=(x, name) :: env; anons=anons+1 };
      name

let rec pp_type ctx lvl = function
  | TVar x -> pp_context_lookup (AnonVar x) ctx
  | TADT (x, tps) -> 
    let x = pp_context_lookup (NamedVar x) ctx in
    let tps = pp_list "," ctx 1 tps |> pp_at_level 1 (List.length tps) in
    pp_at_level 0 lvl
      (Printf.sprintf "%s %s" x tps)
  | TUnit  -> "Unit"
  | TEmpty -> "Empty"
  | TBool  -> "Bool"
  | TInt   -> "Int"
  | TArrow(arr, targ, tres) ->
      let arr_str =
        let module Effect = Core.Effect in
        match Arrow.view arr with
        | EffPure, FldUnfolded -> "->"
        | EffPure, FldFolded   -> ","
        | EffImpure, FldUnfolded -> "->[]"
        | EffImpure, FldFolded   -> ",'"
      in
      pp_at_level 0 lvl
        (Printf.sprintf "%s %s %s" (pp_type ctx 0 targ) arr_str (pp_type ctx 0 tres))
  | TPair(tp1, tp2) ->
    pp_at_level 2 lvl
      (Printf.sprintf "%s * %s"
        (pp_type ctx 3 tp1)
        (pp_type ctx 3 tp2))
  (* | TForallT (_tvars, tp) -> pp_type ctx lvl tp *)
  | TForallT (tvars, tp) -> 
    let tvars = List.map (fun v -> pp_context_lookup (AnonVar v) ctx) tvars in
    pp_at_level 3 lvl
      (Printf.sprintf "∀ %s. %s" (String.concat "," tvars) (pp_type ctx 0 tp))

and pp_list separator ctx lvl tps =
  String.concat separator @@ List.map (pp_type ctx lvl) tps

let pp_type ctx = pp_type ctx 0

let string_of_type = pp_type (pp_context ())
