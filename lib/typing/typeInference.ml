(** Type inference (for simple types) *)

open Core.Imast
open Utils
module Imast = Core.Imast
module Utils = Core.Utils

(* ========================================================================= *)
(* Type inference *)


let make_mono tp eff =
  Schema.typ_mono tp, eff

let get_tp ({typ;_} : Schema.typ expr) =
  Schema.get_template typ

let rec is_value (e : 'a expr) =
  match e.data with
  | EUnit | EBool _ | ENum _ | EVar _ | EExtern _
  | EFn _ | EFix _  -> true
  | ECtor (_, _,e) -> is_value e
  | EPair (e1, e2) ->
    is_value e1 && is_value e2
  | EApp (_, _) | ELet (_, _, _) | EFst _ | ESnd _ | EIf (_, _, _)
  | ESeq (_, _) | ETypeAlias (_, _, _) | EType (_, _, _) | EMatch (_, _) ->
    false

(** inference function *)
let rec infer env (node : Imast.expl_type Imast.expr) =
  let state = !counter in
  mark "enter infer";
  dump_expr' node;
  mark "+++Pos: (%s)" (Utils.string_of_pp node.start_pos node.end_pos);
  let data, typ = tr_expr env node in
  mark "---Pos: (%s)" (Utils.string_of_pp node.start_pos node.end_pos);
  dump_type typ;
  Unify.equal node typ (tr_type node env node.typ);
  let res = { node with data; typ=Schema.typ_mono typ } in
  mark "exiting infer [%d]" state;
  dump_expr res;
  res

and tr_type node env explicit_type : Type.t =
  mark "tr_type %s" (Imast.pp_expl_type VarTbl.find explicit_type);
  let unwrap = unwrap node env in
  let rec inner node env = function
    | Imast.TUnit -> Type.t_unit
    | Imast.THole ->
      let uv = Env.fresh_uvar env in
      mark "inner fresh_uvar: %s"
      (PrettyPrinter.pp_type ~ctx:(get_ctx()) uv);
      uv
    | Imast.TBool -> Type.t_bool
    | Imast.TInt  -> Type.t_int
    | Imast.TArrow(tp1, tp2) ->
      let tp1 = inner node env tp1 in
      let tp2 = inner node env tp2 in
      Type.t_arrow tp1 tp2
    | Imast.TPair (tp1, tp2) ->
      let tp1 = inner node env tp1 in
      let tp2 = inner node env tp2 in
      Type.t_pair tp1 tp2
    | Imast.TVar name -> 
      let tp = Env.lookup_delta env name |> unwrap name in
      if Type.TVarSet.is_empty (Schema.get_arguments tp)
      then Env.instantiate env tp |> fst
      else
        Utils.report_error node
          "Alias used without parameters: %s"
          (VarTbl.find name)
    | Imast.TAlias (name, tps) ->
      let typ = Env.lookup_delta env name |> unwrap name in
      let set = Schema.get_arguments typ in
      if Type.TVarSet.is_empty set then
        Utils.report_error node
          "Alias used without parameters: %s"
          (VarTbl.find name)
      else
        let mapping = List.map (inner node env) tps
          |> List.to_seq
          |> Seq.zip (Type.TVarSet.to_seq set)
          |> Type.TVarMap.of_seq
        in
        Env.instantiate env ~mapping typ |> fst
  in inner node env explicit_type

and tr_expr env (e : Imast.expl_type Imast.expr) =
  let unwrap name = unwrap e env name in
  let gen_mapping uvar_set =
    let uvar_seq = Type.TVarSet.to_list uvar_set
      |> List.map (fun uvar -> (uvar, Env.fresh_uvar env))
      |> List.to_seq in
    let mapping = Type.TVarMap.of_seq uvar_seq in
    let instance_args = Seq.unzip uvar_seq
      |> snd
      |> List.of_seq
    in mapping, instance_args
  in
  let tr_var env ((name,typ) : expl_type var_def) =
      let expl = tr_type e env typ in
      let new_typ = Schema.typ_mono expl in
      (name, new_typ), expl
  in
  match e.data with
  | EUnit   -> EUnit,   Type.t_unit
  | EBool b -> EBool b, Type.t_bool
  | ENum  n -> ENum  n, Type.t_int

  | EExtern (name, eff, typ) ->
    let expl = tr_type e env typ in
    EExtern (name, eff, Schema.typ_mono expl),
    expl

  | EVar  (name,_) ->
    let schema = Env.lookup_gamma env name
      |> unwrap name in
    let instantiated, args = Env.instantiate env schema in
    mark "EVar(%s,[%s]) : %s" (VarTbl.find name)
      (List.map (PrettyPrinter.pp_type ~ctx:(get_ctx())) args
      |> String.concat ",")
      (PrettyPrinter.pp_type ~ctx:(get_ctx()) instantiated);
    mark "EVar(%s, schema) = %s" (VarTbl.find name) (pp_typ schema);
    EVar (name, List.map Schema.typ_mono args), instantiated

  | EFn(x, body) ->
    let state = !counter in
    mark "entering EFn(%s,body)" (VarTbl.find (fst x));
    let var, typ = tr_var env x in
    dump_var var;
    let env = Env.extend_gamma env var in
    let body' = infer env body in
    mark "exiting EFn(%s,body) [%d]" (VarTbl.find (fst x)) state;
    EFn (var, body'),
    Type.t_arrow typ (get_tp body')

  | EFix(f, x, body) ->
    let state = !counter in
    mark "entering EFix(%s,body)" (VarTbl.find (fst x));
    let x', typ = tr_var env x in
    dump_var x';
    let env = Env.extend_gamma env x' in
    let f', f_tp = tr_var env f in
    dump_var f';
    let tres = Env.fresh_uvar env in
    dump_type2 "---" tres f_tp;
    let f_tp' = Type.t_arrow typ tres in
    Unify.equal e f_tp f_tp';
    let env = Env.extend_gamma env f' in
    let body' = infer_and_check_type env body tres in
    mark "exiting EFix [%d]" state;
    EFix(f', x', body'), f_tp

  | EApp(e1, e2) ->
    let state = !counter in
    mark "entering EApp [%d]" state;
    let e1' = infer env e1 in
    mark "EApp e1'.typ [%d] : %s" state (pp_typ e1'.typ);
    let e2' = infer env e2 in
    mark "EApp e2'.typ [%d] : %s" state (pp_typ e2'.typ);
    let tres = Env.fresh_uvar env in
    Type.t_arrow (Schema.get_template e2'.typ) tres
    |> Unify.equal e (Schema.get_template e1'.typ);
    mark "exiting EApp [%d] : %s" state
      (PrettyPrinter.pp_type ~ctx:(get_ctx()) tres);
    EApp(e1', e2'), tres

  | ELet((x,tp), e1, e2) ->
    let env' = Env.increase_level_major env in
    let tp = tr_type e env' tp in
    let state = !counter in
    mark "ELet entered %s [%d]" (VarTbl.find x) state;
    dump_var (x, Schema.typ_mono tp);
    let e1' = infer_and_check_type env' e1 tp in
    let x = if is_value e1'
      then x, Env.generalize env' tp
      else x, Schema.typ_mono (get_tp e1') in
    mark "ELet generalised %s [%d]" (VarTbl.find @@ fst x) state;
    dump_var ~register:false x;
    let e2' = infer (Env.extend_gamma env x) e2 in
    ELet(x, e1', e2'), get_tp e2'

  | EPair(e1, e2) ->
    let e1' = infer env e1 in
    let e2' = infer env e2 in
    EPair(e1', e2'), Type.t_pair (get_tp e1') (get_tp e2')

  | EFst e ->
    let tp1 = Env.fresh_uvar env in
    let tp2 = Env.fresh_uvar env in
    let e' = infer_and_check_type env e (Type.t_pair tp1 tp2) in
    EFst e', tp1
  | ESnd e ->
    let tp1 = Env.fresh_uvar env in
    let tp2 = Env.fresh_uvar env in
    let e' = infer_and_check_type env e (Type.t_pair tp1 tp2) in
    ESnd e', tp2

  | EIf(e1, e2, e3) ->
    let e1' = infer_and_check_type env e1 Type.t_bool in
    let e2' = infer env e2 in
    let res_tp = get_tp e2' in
    let e3' = infer_and_check_type env e3 res_tp in
    EIf(e1', e2', e3'), res_tp

  | ESeq(e1, e2) ->
    let e1' = infer_and_check_type env e1 Type.t_unit in
    let e2' = infer env e2 in
    ESeq(e1', e2'), get_tp e2'

  | EType ((name,arg_list) as alias, ctor_defs, rest) ->
    let out_type = Env.fresh_uvar env in
    let env = Env.increase_level_minor env in
    let arg_list = List.map (fun x -> (x, Type.TVar.fresh ())) arg_list in
    let set = List.map snd arg_list |> Type.TVarSet.of_list in
    let arg_list = List.map (fun (x,t) -> x, Type.t_var t) arg_list in
    let tvars = List.map snd arg_list in
    let env = Env.extend_delta_with_adt env name tvars set in
    let env' = Env.extend_delta_of_list env arg_list in
    let f (name, typ) =
      let typ = tr_type e env' typ  in
      name, Schema.typ_schema set typ in
    let ctor_defs' = List.map f ctor_defs in
    let env = Env.extend_by_ctors env ctor_defs' name tvars set  in
    let rest' = infer_and_check_type env rest out_type in
    EType(alias, ctor_defs', rest'), get_tp rest'

  | ECtor (name, _, body) ->
    let expected_typ, alias_typ = Env.lookup_ctor env name |> unwrap name in
    let var_set = Schema.get_arguments alias_typ in
    let mapping, alias_args = gen_mapping var_set in
    let expected_type, _ = Env.instantiate ~mapping env expected_typ in
    let alias_t, _ = Env.instantiate ~mapping env alias_typ in
    let body' = infer_and_check_type env body expected_type in
    ECtor (name, List.map Schema.typ_mono alias_args, body'), alias_t

  | ETypeAlias ((name, arg_list) as alias, typ, rest) ->
    let arg_list = List.map (fun x -> (x, Type.TVar.fresh ())) arg_list in
    let set = List.map snd arg_list |> Type.TVarSet.of_list in
    let arg_list = List.map (fun (x,t) -> x, Type.t_var t) arg_list in
    let env' = Env.extend_delta_of_list env arg_list in
    let typ' = tr_type e env' typ |> Schema.typ_schema set in
    let env = Env.extend_delta_with_alias env (name, typ') in
    let rest' = infer env rest in
    ETypeAlias(alias, typ', rest'), get_tp rest'

  | EMatch (sub_expr, ((ctor_name, _, _) :: _ as clauses)) ->
    mark "EMatch entered";
    let _, adt_typ = Env.lookup_ctor env ctor_name |> unwrap ctor_name in
    let var_set = Schema.get_arguments adt_typ in
    let mapping, instance_args = gen_mapping var_set in
    let adt_t, _ = Env.instantiate ~mapping env adt_typ in
    let sub_expr' = infer_and_check_type env sub_expr adt_t in
    mark "EMatch subexpr infered : %s" (pp_typ sub_expr'.typ);
    let out_type = Env.fresh_uvar env in
    let f (ctor_name, (var_name, var_type), e) =
      let typ, _ = Env.lookup_ctor env ctor_name |> unwrap ctor_name in
      let expected_type, _ = Env.instantiate ~mapping env typ in
      Unify.equal e expected_type (tr_type e env var_type);
      let typ = Schema.typ_mono expected_type in
      let env = Env.extend_gamma env (var_name, typ) in
      ctor_name, (var_name, typ), infer_and_check_type env e out_type
    in
    let clauses' = List.map f clauses in
    EMatch (sub_expr', clauses'), out_type

  | EMatch (sub_expr, []) ->
    let sub_expr' = infer_and_check_type env sub_expr Type.t_empty in
    EMatch (sub_expr', []), Env.fresh_uvar env

and infer_and_check_type env e expected =
  mark "infer_and_check_type entered";
  let e' = infer env e in
  Unify.equal e' expected (get_tp e');
  e'

type program = Schema.typ Imast.expr

let infer (p : Imast.program) : program =
  let data, typ = tr_expr Env.empty p in
  (* should be a better way to return generalized type *)
  let typ = Schema.generalize Type.Level.starting typ in
  { p with data; typ }
