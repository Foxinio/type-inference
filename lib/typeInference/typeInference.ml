(** Type inference (for simple types) *)

open Core.Imast
open Core

open Unify

(* ========================================================================= *)
(* Type inference *)

let node_with_type ({ data; start_pos; end_pos;_} : ('a, 'b) Ast.node) (typ : Type.t) : ('a, Type.t) Ast.node =
  { data; typ; start_pos; end_pos }

let var_name env var =
    Env.lookup_var_name env var |>
      Option.value ~default:"<unknown>"

let unwrap node env var opt =
  match opt with
  | Some t -> t
  | None ->
    let name = var_name env var in
    Utils.report_error node "Undefined variable: %s" name

let ensure_well_scoped e env ((alias_name, alias_args) as alias) t =
  let unwrap = unwrap e env in
  let rec check_scope_v default t = match Type.view t with
    | TUVar u | TGVar (u, None) ->
      Type.uvar_disallow_alias u alias_name;
    | TADT (alias_name', _) when IMAstVar.compare alias_name alias_name' = 0 ->
      Utils.report_error e "alias out of scope %s" (var_name env alias_name')
    | tp -> default tp
  in Type.iter check_scope_v t

let ensure_no_hole e =
  let f default = function
    | Imast.THole -> 
      Utils.report_error e "Type constructors can't have holes in them"
    | tp -> default tp
  in List.iter (fun (_, t) -> Imast.type_iter f t)

let uvar_of_view t = match Type.view t with
  | TUVar u | TGVar (u,_) -> u
  | _ -> failwith "Internal error, passed non uvar to uvar getter"

(** Typing environments *)
let rec infer env (node : Imast.expl_type Imast.expr) : Type.t Imast.expr =
  let data, typ = infer_type env node in
  unify typ (convert_type node env node.typ);
  { node with data; typ }
and convert_type node env explicit_type : Type.t =
  let unwrap = unwrap node env in
  match explicit_type with
  | Imast.TUnit -> Type.t_unit
  | Imast.THole -> Type.fresh_uvar ()
  | Imast.TBool -> Type.t_bool
  | Imast.TInt  -> Type.t_int
  | Imast.TArrow(tps, tp) ->
    let tps = List.map (convert_type node env) tps in
    let tp = convert_type node env tp in
    Type.t_arrow tps tp
  | Imast.TProd tps ->
    let tps = List.map (convert_type node env) tps in
    Type.t_prod tps
  | Imast.TVar v -> 
    let (typ, set) = Env.lookup_delta env v |> unwrap v in
    if Type.UVarSet.is_empty set then Type.instantiate typ
    else 
      Utils.report_error node "Alias used without parameters: %s" (var_name env v)
  | Imast.TAlias (name, tps) ->
    let (typ, set) = Env.lookup_delta env name |> unwrap name in
    let mapping = List.map (convert_type node env) tps |>
          List.to_seq |>
          Seq.zip (Type.UVarSet.to_seq set) |>
          Type.UVarMap.of_seq in
    Type.instantiate ~mapping typ

and infer_type env (e : Imast.expl_type Imast.expr) : Type.t Imast.expr_data * Type.t =
  let unwrap name = unwrap e env name in
  let get_alias_from_ctor env ctor_name =
    let _, (alias_name, _) = Env.lookup_ctor env ctor_name |> unwrap ctor_name in
    alias_name, Env.lookup_delta env alias_name |> unwrap alias_name |> snd
  and gen_mapping uvar_set =
    let uvar_seq = Type.UVarSet.to_seq uvar_set |>
      Seq.map (fun uvar -> (uvar, Type.fresh_uvar ())) in
    let mapping = Type.UVarMap.of_seq uvar_seq in
    let instance_args = Seq.unzip uvar_seq |> snd |> List.of_seq in
    mapping, instance_args
  in
  let extend_list xs env =
    let extend (tps, env) x =
      let new_tp = Type.fresh_gvar () in
      unify new_tp (snd x);
      new_tp :: tps, Env.extend_gamma env x (Type.typ_mono new_tp)
    in
    List.fold_left extend ([], env) xs
  and convert_var env ((name,typ) : expl_type var) =
    name, convert_type e env typ
  in
  match e.data with
  | EUnit   -> EUnit,   Type.t_unit
  | EBool b -> EBool b, Type.t_bool
  | ENum  n -> ENum  n, Type.t_int
  | EVar  (name,typ) ->
    let typ' = convert_type e env typ in
    let instantiated = Env.lookup_gamma env name
      |> unwrap name in
    EVar (name, typ'), instantiated
  | EFn(xs, body) ->
    let xs : Type.t var list = List.map (convert_var env) xs in
    let tps, env = extend_list xs env in
    let body' = infer env body in
    EFn (xs, body'), Type.t_arrow tps body'.typ
  | EFix(f, xs, body) ->
    let xs = List.map (convert_var env) xs in
    let tps, env = extend_list xs env in
    let tp2 = Type.fresh_uvar () in
    let f = convert_var env f in
    let f_tp = Type.t_arrow tps tp2 in
    let env = Env.extend_gamma env f (Type.typ_mono f_tp) in
    let body' = check_type env body tp2 in
    EFix(f, xs, body'), f_tp
  | EApp(e1, es) ->
    let generate _ = Type.fresh_uvar () in
    let tps = List.map generate es in
    let tp1 = Type.fresh_uvar () in
    let e1' = check_type env e1 (Type.t_arrow tps tp1) in
    let es' = List.map2 (fun e tp -> check_type env e tp) es tps in
    EApp(e1', es'), tp1
  | ELet(x, e1, e2) ->
    let e1' = infer env e1 in
    let x = convert_var env x in
    let tp = Type.generalize (Env.get_uvars env) e1'.typ in
    let e2' = infer (Env.extend_gamma env x tp) e2 in
    ELet(x, e1', e2'), e2'.typ
  | EPair(e1, e2) ->
    let e1' = infer env e1 in
    let e2' = infer env e2 in
    EPair(e1', e2'), Type.t_pair e1'.typ e2'.typ
  | EFst e ->
    let tp1 = Type.fresh_uvar () in
    let tp2 = Type.fresh_uvar () in
    let e' = check_type env e (Type.t_pair tp1 tp2) in
    EFst e', tp1
  | ESnd e ->
    let tp1 = Type.fresh_uvar () in
    let tp2 = Type.fresh_uvar () in
    let e' = check_type env e (Type.t_pair tp1 tp2) in
    ESnd e', tp2
  | EIf(e1, e2, e3) ->
    let e1' = check_type env e1 Type.t_bool in
    let e2' = infer env e2 in
    let e3' = check_type env e3 e2'.typ in
    EIf(e1', e2', e3'), e2'.typ
  | ESeq(e1, e2) ->
    let e1' = check_type env e1 Type.t_unit in
    let e2' = infer env e2 in
    ESeq(e1', e2'), e2'.typ
  | EAbsurd e ->
    let e' = check_type env e Type.t_empty in
    EAbsurd e', Type.fresh_uvar ()

  | EType ((name,arg_list) as alias, ctor_defs, rest) ->
    ensure_no_hole e ctor_defs;
    let arg_list = List.map (fun x -> (x, Type.fresh_uvar ())) arg_list in
    let uvars = List.map (fun (a,b) -> b) arg_list in
    let set = List.map uvar_of_view uvars |> Type.UVarSet.of_list in
    let schema_typ = Type.t_adt name uvars in
    let env = Env.extend_delta env (name, Type.typ_schema set schema_typ) set in
    let env' = Env.extend_delta_of_list env arg_list in
    let ctor_defs = List.map (convert_var env') ctor_defs in
    let f (name, typ) = name, Type.typ_schema set typ in
    let ctor_defs' = List.map f ctor_defs in
    let env = Env.extend_by_ctors env ctor_defs' (name, set) in
    let rest' = infer env rest in
    ensure_well_scoped e env alias rest'.typ;
    EType(alias, ctor_defs, rest'), rest'.typ

  | ECtor (name, body) ->
    let typ, (alias_name, uvar_set) = Env.lookup_ctor env name |> unwrap name in
    let mapping, alias_args = gen_mapping uvar_set in
    let expected_type = Type.instantiate ~mapping typ in
    let body' = check_type env body expected_type in
    ECtor (alias_name, body'), Type.t_adt alias_name alias_args

  | ETypeAlias ((name, arg_list) as alias, typ, rest) ->
    let arg_list = List.map (fun x -> (x, Type.fresh_uvar ())) arg_list in
    let env' = Env.extend_delta_of_list env arg_list in
    let set = List.map (fun (a,b) -> uvar_of_view b) arg_list |> Type.UVarSet.of_list in
    let typ = convert_type e env' typ in
    let typ' = Type.typ_schema set typ in
    let env = Env.extend_delta env (name, typ') set in
    let rest' = infer env rest in
    ETypeAlias(alias, typ, rest'), rest'.typ

  | EMatch (sub_expr, ((ctor_name, _, _) :: _ as clauses)) ->
    let alias_name, uvar_set = get_alias_from_ctor env ctor_name in
    let mapping, instance_args = gen_mapping uvar_set in
    let adt_type = Type.t_adt alias_name instance_args in
    let sub_expr' = check_type env sub_expr adt_type in
    let out_type = Type.fresh_uvar () in
    let f (ctor_name, (var_name, var_type), e) =
      let typ, _ = Env.lookup_ctor env ctor_name |> unwrap ctor_name in
      let expected_type = Type.instantiate ~mapping typ in
      unify expected_type (convert_type e env var_type);
      let env = Env.extend_gamma env (var_name, expected_type)
        (Type.typ_mono expected_type) in
      ctor_name, (var_name, expected_type), check_type env e out_type
    in
    let clauses' = List.map f clauses in
    EMatch (sub_expr', clauses'), out_type
  | EMatch _ ->
    Utils.report_error e "cannot have match with no clauses"

and check_type env e tp =
  let open PrettyPrinter in
  let e' = infer env e in
  try
    unify tp e'.typ;
    e'
  with
  | Cannot_unify ->
    let ctx = pp_context () in
    Utils.report_error e
      "This expression has type %s, but an expression was expected of type %s."
      (pp_type ctx 0 e'.typ)
      (pp_type ctx 0 tp)

type program = Type.t Imast.expr * string Imast.VarTbl.t

let infer ((p, env) : Imast.program) : program =
  let node = infer (Env.of_var_names env) p in
  node, env
