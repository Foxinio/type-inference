(** Type inference (for simple types) *)

open Core.Ast
open Core

(** Internal representation of types *)
module Type : sig
  type t
  type uvar
  type view =
    | TUnit
    | TEmpty
    | TBool
    | TInt
    | TGVar   of uvar * view option
    | TUVar   of uvar * view option
    | TArrow  of view * t
    | TProd   of t list
    | TCoProd of t list

  val fresh_uvar : unit -> t
  val fresh_gvar : unit -> t

  val t_unit   : t
  val t_empty  : t
  val t_bool   : t
  val t_int    : t
  val t_arrow  : t list -> t -> t
  val t_pair   : t -> t -> t
  val t_copair : t -> t -> t
  val t_prod   : t list -> t
  val t_coprod   : t list -> t

  val view : t -> view

  val set_uvar : uvar -> t -> unit

  exception Cannot_compare of t * t
  (* val compare : t -> t -> int *)
end = struct
  type t = 
    | TIUnit
    | TIEmpty
    | TIBool
    | TIInt
    | TIGVar   of uvar
    | TIUVar   of uvar
    | TIArrow  of t * t
    | TIProd   of t list
    | TICoProd of t list

  and uvar = t option ref
  and view =
    | TUnit
    | TEmpty
    | TBool
    | TInt
    | TGVar   of uvar * view option
    | TUVar   of uvar * view option
    | TArrow  of view * t
    | TProd   of t list
    | TCoProd of t list

  let fresh_uvar () = TIUVar (ref None)
  let fresh_gvar () = TIGVar (ref None)
  let filled_uvar tp = TIUVar (ref (Some tp))

  let t_unit  = TIUnit
  let t_empty = TIEmpty
  let t_bool  = TIBool
  let t_int   = TIInt
  let t_arrow  tps tp2 = 
    filled_uvar (TIArrow(TIProd(tps), tp2))
  let t_pair   tp1 tp2 = TIProd([tp1; tp2])
  let t_copair tp1 tp2 = TICoProd([tp1; tp2])
  let t_prod   tps = TIProd(tps)
  let t_coprod tps = TICoProd(tps)

  let rec t_of_view = function
    | TUVar (x, _) -> TIUVar x
    | TGVar (x, _) -> TIGVar x
    | TUnit -> TIUnit
    | TEmpty -> TIEmpty
    | TBool -> TIBool
    | TInt -> TIInt
    | TArrow(tp1, tp2) -> TIArrow(t_of_view tp1, tp2)
    | TProd tps -> TIProd tps
    | TCoProd tps -> TICoProd tps

  let rec view tp =
    let shorten_path x =
      match !x with
      | None -> ()
      | Some tp ->
        let tp = view tp in
        x := Some (t_of_view tp)
    in
    match tp with
    | TIUVar x ->
        shorten_path x;
        TUVar (x, Option.map view (!x))
    | TIGVar x ->
        shorten_path x;
        TGVar (x, Option.map view (!x))
    | TIUnit -> TUnit
    | TIEmpty -> TEmpty
    | TIBool -> TBool
    | TIInt -> TInt
    | TIArrow(tp1, tp2) -> TArrow(view tp1, tp2)
    | TIProd tps -> TProd tps
    | TICoProd tps -> TCoProd tps


  exception Cannot_compare of t * t

  let rec set_uvar_int x tp general =
    match !x with
    | None -> x := Some tp
    | Some tp_current when general && compare tp tp_current >= 0 ->
        x := Some tp
    | Some _ -> assert false

  and reconstruct (new_tp : t) (currrnet_tp : t) =
    let rec reconstruct_arrows (tpsa, resa) (tpsb, resb) =
      match tpsa, tpsb with
      | tpa :: tpsa, tpb :: tpsb ->
          (* because arguments in arrows are contravariant these are reversed *)
          let tp = reconstruct tpb tpa in
          let rest, res = reconstruct_arrows (tpsa, resa) (tpsb, resb) in
          tp :: rest, res
      | [], _ :: _ ->
          [], reconstruct resa (TIArrow (TIProd tpsb, resb))
      | _ :: _, [] ->
          begin match view resb with
          | TGVar _
          | TUVar _
          | TArrow (TProd _, _) ->
              [], reconstruct (TIArrow (TIProd tpsa, resa)) resb
          | _ -> raise (Cannot_compare (new_tp, currrnet_tp))
          end
      | [], [] ->
          [], reconstruct resa resb
    in
    let uvar_map x tp fn =
      match !x with
      | None ->
          x := Some tp;
          tp
      | Some tp ->
          let res = fn tp in
          x := Some res;
          res
    in
    match new_tp, currrnet_tp with
    | TIUVar x, _ ->
        uvar_map x currrnet_tp (fun _ -> raise (Cannot_compare (new_tp, currrnet_tp)))
    | TIGVar x, _ ->
        uvar_map x currrnet_tp (fun tp -> reconstruct tp currrnet_tp)
    | _, TIUVar x ->
        uvar_map x new_tp (fun _ -> raise (Cannot_compare (new_tp, currrnet_tp)))
    | _, TIGVar x ->
        uvar_map x new_tp (fun tp -> reconstruct new_tp tp)
    | TIUnit, TIUnit -> TIUnit
    | _, TIUnit    -> TIUnit

    | TIEmpty, TIEmpty -> TIEmpty
    | TIEmpty, _     -> TIEmpty

    | TIBool, TIBool -> TIBool
    | TIInt, TIInt -> TIInt

    | TIArrow (TIProd tpsa, tp_resa),
      TIArrow (TIProd tpsb, tp_resb) ->
        let args, res = reconstruct_arrows (tpsa, tp_resa) (tpsb, tp_resb) in
        t_arrow args res

    | TIArrow(ta1, tb1), TIArrow(ta2, tb2) ->
        let res1 = reconstruct ta2 ta1 in
        let res2 = reconstruct tb1 tb2 in
        TIArrow(res1, res2)
    | TIProd(ts1), TIProd(ts2) when List.length ts1 = List.length ts2 ->
      TIProd (List.map2 reconstruct ts1 ts2)
    | TICoProd(ts1), TICoProd(ts2) when List.length ts1 = List.length ts2 ->
      TICoProd (List.map2 reconstruct ts1 ts2)
    | _, _ -> raise (Cannot_compare (new_tp, currrnet_tp))


  let set_uvar x tp =
    set_uvar_int x tp false
  let set_gvar x tp =
    set_uvar_int x tp true
end
open Type

(* ========================================================================= *)
(* Pretty printing of types *)

(** Creates fresh pretty-printing context *)
let pp_context () = ref []

let pp_at_level l lvl str =
  if lvl > l then Printf.sprintf "(%s)" str
  else str


let rec pp_type ctx lvl tp =
  let rec matcher lvl = function
    | TUnit  -> "Unit"
    | TEmpty -> "Empty"
    | TBool  -> "Bool"
    | TInt   -> "Int"
    | TUVar (x, None) ->
      begin match List.assq_opt x !ctx with
      | Some str -> str
      | None ->
        let name = Printf.sprintf "x%d" (List.length !ctx) in
        ctx := (x, name) :: !ctx;
        name
      end
    | TUVar (x, Some tp) ->
        matcher lvl tp
    | TGVar (x, None) ->
      begin match List.assq_opt x !ctx with
      | Some str -> str
      | None ->
        let name = Printf.sprintf "x%d" (List.length !ctx) in
        ctx := (x, name) :: !ctx;
        name
      end
    | TGVar (x, Some tp) ->
        matcher lvl tp
    | TArrow(tp1, tp2) ->
      pp_at_level 0 lvl
        (Printf.sprintf "%s -> %s" (matcher 1 tp1) (pp_type ctx 0 tp2))
    | TProd(tps) ->
      pp_at_level 2 lvl
        (Printf.sprintf "%s" (pp_list "*" ctx 3 tps))
    | TCoProd(tps) ->
      pp_at_level 1 lvl
        (Printf.sprintf "%s" (pp_list "+" ctx 2 tps))
    and pp_list separator ctx lvl = function
    | [ tp ] -> pp_type ctx (lvl-1) tp
    | tp :: tps ->
        Printf.sprintf "%s %s %s" (pp_type ctx lvl tp) separator (pp_list separator ctx lvl tps)
    | [] -> "Unit"
  in Type.view tp |> matcher lvl

let string_of_type = pp_type (pp_context ()) 0

(* ========================================================================= *)
(* Unification *)

exception Cannot_unify

let rec contains_uvar x tp =
  let rec list_contains_uvar = function
    | [] -> false
    | tp :: tps -> contains_uvar x tp || list_contains_uvar tps
  and contains_uvar_int = function
    | TUVar (y, None) -> x == y
    | TUVar (_, Some tp)
    | TGVar (_, Some tp) -> contains_uvar_int tp
    | TUnit | TEmpty | TBool | TInt | TGVar (_, None) -> false
    | TArrow(tp1, tp2) ->
      contains_uvar_int tp1 || contains_uvar x tp2
    | TProd(tps) | TCoProd(tps) ->
      list_contains_uvar tps
  in Type.view tp |> contains_uvar_int


let unify_with_uvar x tp =
  if contains_uvar x tp then raise Cannot_unify
  else try
    Type.set_uvar x tp
  with Type.Cannot_compare _ ->
    raise Cannot_unify


let rec unify tp1 tp2 =
  let rec unify_int tpv1 tpv2 =
    match tpv1, tpv2 with
    | TUVar (x, None), TUVar (y, None)
    | TGVar (x, None), TGVar (y, None) when x == y -> ()

    | _, TUVar (x, None) -> unify_with_uvar x tp1
    | TUVar (x, None), _ -> unify_with_uvar x tp2

    | _, TGVar (x, None) -> unify_with_uvar x tp1
    | TGVar (x, None), _ -> unify_with_uvar x tp2

    | TGVar (x, Some(TArrow _)), TArrow _ ->
        unify_with_uvar x tp2
    | TArrow _, TGVar (x, Some(TArrow _)) ->
        unify_with_uvar x tp1

    | TUVar (_, Some tp1), tp2
    | TGVar (_, Some tp1), tp2 -> unify_int tp1 tp2
    | tp1, TUVar (_, Some tp2)
    | tp1, TGVar (_, Some tp2) -> unify_int tp1 tp2

    | TUnit, TUnit -> ()
    | TUnit, _ -> raise Cannot_unify

    | TEmpty, TEmpty -> ()
    | TEmpty, _ -> raise Cannot_unify

    | TBool, TBool -> ()
    | TBool, _ -> raise Cannot_unify

    | TInt, TInt -> ()
    | TInt, _ -> raise Cannot_unify

    | TArrow(ta1, tb1), TArrow(ta2, tb2) ->
      unify_int ta1 ta2;
      unify tb1 tb2
    | TArrow _, _ -> raise Cannot_unify

    | TProd(ts1), TProd(ts2)
    | TCoProd(ts1), TCoProd(ts2) ->
      List.iter2 unify ts1 ts2
    | TCoProd _, _
    | TProd _, _ -> raise Cannot_unify
  in
  unify_int (Type.view tp1) (Type.view tp2)

(* ========================================================================= *)
(* Type inference *)

(** Typing environments *)
module Env : sig
  type t

  val empty : t

  val extend : t -> Ast.var -> Type.t -> t

  val lookup : t -> Ast.var -> Type.t option
end = struct
  module VarMap = Map.Make(String)

  type t = Type.t VarMap.t

  let empty = VarMap.empty

  let extend env x tp = VarMap.add x tp env

  let lookup env x = VarMap.find_opt x env
end

let rec infer_type env (e : Ast.expr) =
  let extend_list xs env =
    let extend (tps, env) x = 
      let new_tp = Type.fresh_gvar () in
      new_tp :: tps, Env.extend env x new_tp
    in
    List.fold_left extend ([], env) xs
  in
  match e.data with
  | EUnit   -> Type.t_unit
  | EBool _ -> Type.t_bool
  | ENum  _ -> Type.t_int
  | EVar  x ->
    begin match Env.lookup env x with
    | Some tp -> tp
    | None ->
      Utils.report_error e "Unbound variable %s" x
    end
  | EFn(xs, body) ->
    let tps, env = extend_list xs env in
    let tp2 = infer_type env body in
    Type.t_arrow tps tp2
  | EFix(f, xs, body) ->
    let tps, env = extend_list xs env in
    let tp2 = Type.fresh_uvar () in
    let f_tp = Type.t_arrow tps tp2 in
    check_type (Env.extend env f f_tp) body tp2;
    f_tp
  | EApp(e1, es) ->
    let generate _ = Type.fresh_uvar () in
    let tps = List.map generate es in
    let tp1 = Type.fresh_uvar () in
    check_type env e1 (Type.t_arrow tps tp1);
    List.iter2 (fun e tp -> check_type env e tp) es tps;
    tp1
  | ELet(x, e1, e2) ->
    let tp1 = infer_type env e1 in
    infer_type (Env.extend env x tp1) e2
  | EPair(e1, e2) ->
    let tp1 = infer_type env e1 in
    let tp2 = infer_type env e2 in
    Type.t_pair tp1 tp2
  | EFst e ->
    let tp1 = Type.fresh_uvar () in
    let tp2 = Type.fresh_uvar () in
    check_type env e (Type.t_pair tp1 tp2);
    tp1
  | ESnd e ->
    let tp1 = Type.fresh_uvar () in
    let tp2 = Type.fresh_uvar () in
    check_type env e (Type.t_pair tp1 tp2);
    tp2
  | EInl e ->
    let tp1 = infer_type env e in
    let tp2 = Type.fresh_uvar () in
    Type.t_copair tp1 tp2
  | EInr e ->
    let tp1 = Type.fresh_uvar () in
    let tp2 = infer_type env e in
    Type.t_copair tp1 tp2
  | ECase(e, (x1, e1), (x2, e2)) ->
    let tp1 = Type.fresh_uvar () in
    let tp2 = Type.fresh_uvar () in
    check_type env e (Type.t_copair tp1 tp2);
    let tp = infer_type (Env.extend env x1 tp1) e1 in
    check_type (Env.extend env x2 tp2) e2 tp;
    tp
  | EIf(e1, e2, e3) ->
    check_type env e1 Type.t_bool;
    let tp = infer_type env e2 in
    check_type env e3 tp;
    tp
  | ESeq(e1, e2) ->
    check_type env e1 Type.t_unit;
    infer_type env e2
  | EAbsurd e ->
    check_type env e Type.t_empty;
    Type.fresh_uvar ()
  (* | ESelect _ | ERecord _  *)
  | ECtor _ | EMatch _ | EMatchEmpty _ ->
    (* TODO: not implemented *)
    Utils.report_error e "This language feature is not supported yet!"

and check_type env (e : Ast.expr) tp =
  let tp' = infer_type env e in
  try
    unify tp tp'
  with
  | Cannot_unify ->
    let ctx = pp_context () in
    Utils.report_error e
      "This expression has type %s, but an expression was expected of type %s."
      (pp_type ctx 0 tp')
      (pp_type ctx 0 tp)

let to_system_f p =
  (* TODO: not implemented properly *)
  let _ = infer_type Env.empty p in
  SystemF.ENum 42
