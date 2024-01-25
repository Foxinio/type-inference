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
    | TUVar   of uvar
    | TArrow  of t * t
    | TProd   of t list
    | TCoProd of t list

  val fresh_uvar : unit -> t

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
  val compare : t -> t -> int
end = struct
  type t = view
  and uvar = t option ref
  and view =
    | TUnit
    | TEmpty
    | TBool
    | TInt
    | TUVar   of uvar
    | TArrow  of t * t
    | TProd   of t list
    | TCoProd of t list

  let fresh_uvar () = TUVar (ref None)
  let filled_uvar tp = TUVar (ref (Some tp))

  let t_unit  = TUnit
  let t_empty = TEmpty
  let t_bool  = TBool
  let t_int   = TInt
  let t_arrow  tps tp2 = 
    filled_uvar (TArrow(TProd(tps), tp2))
  let t_pair   tp1 tp2 = TProd([tp1; tp2])
  let t_copair tp1 tp2 = TCoProd([tp1; tp2])
  let t_prod   tps = TProd(tps)
  let t_coprod tps = TCoProd(tps)


  let rec view tp =
    match tp with
    | TUVar x ->
      begin match !x with
      | None -> tp
      | Some tp ->
        let tp = view tp in
        x := Some tp;
        tp
      end
    | _ -> tp

  exception Cannot_compare of t * t

  let rec set_uvar x tp =
    match !x with
    | None -> x := Some tp
    | Some tp_current when compare tp tp_current >= 0 ->
        x := Some tp
    | Some _ -> assert false

  and compare tp1 tp2 =
      let merge_compare cmp1 cmp2 =
        if cmp1 * cmp2 > 0 then cmp1
        else if cmp1 = 0 then cmp2
        else if cmp2 = 0 then cmp1
        else raise (Cannot_compare (tp1, tp2))
      in
      let compare_acc acc l r = 
        let res = compare l r in
        merge_compare res acc
      in
      let rec compare_arrows acc (tps1a, tps1b, tp_resa) (tps2, tp_resb) =
        match tps1a, tps2 with
        | tpa :: tps1a, tpb :: tps2 ->
            let res = compare tpa tpb in
            compare_arrows (merge_compare res acc) (tps1a, tps1b, tp_resa) (tps2, tp_resb)
        | [], _ :: _ ->
            merge_compare acc (compare (TArrow (TProd tps1b, tp_resa))
                                       (TArrow (TProd tps2,  tp_resb)))
        | _ :: _, [] ->
            (* this means previous type was to general and if return type is *)
            begin match view tp_resb with
            | TUVar x ->
              failwith "to implement"
            | TArrow (TProd tps2, tp_resb) ->
                compare_arrows acc (tps1a, tps1b, tp_resa) (tps2, tp_resb)
            | _ -> raise (Cannot_compare (tp1, tp2))
            end
        | [], [] ->
            merge_compare acc (compare tp_resa tp_resb)
      in
    match tp1, tp2 with
    | TUVar x, TUVar y when x == y -> 0
    | TUVar x, TUVar y -> compare_uvar x y

    | TUnit, TUnit -> 0

    | TEmpty, TEmpty -> 0

    | TBool, TBool -> 0
    | TInt, TInt -> 0

    | TArrow (TProd tps1a, TArrow (TProd tps2a, tp_resa)),
      TArrow (TProd tps1b, tp_resb) ->
        compare_arrows 0 (tps1a, tps2a, tp_resa) (tps1b, tp_resb)

    | TArrow (TProd _, _),
      TArrow (TProd _, TArrow (TProd _, _)) ->
        -1 * compare tp2 tp1
    | TArrow(ta1, tb1), TArrow(ta2, tb2) ->
        let cmp1 = compare ta2 ta1 in
        let cmp2 = compare tb1 tb2 in
        merge_compare cmp1 cmp2
    | TProd(ts1), TProd(ts2)
    | TCoProd(ts1), TCoProd(ts2) ->
      List.fold_left2 compare_acc 0 ts1 ts2
    | _, _ -> raise (Cannot_compare (tp1, tp2))
  and compare_uvar x y =
    match !x, !y with
    | Some tp1, Some tp2 -> compare tp1 tp2
    | None, None -> 
        (* [question] Maybe problematic, but seems like good solution *)
        let new_var = fresh_uvar () in
        set_uvar x new_var;
        set_uvar y new_var;
        0
    | _, _ -> raise (Cannot_compare (TUVar x, TUVar y))


end

(* ========================================================================= *)
(* Pretty printing of types *)

(** Creates fresh pretty-printing context *)
let pp_context () = ref []

let pp_at_level l lvl str =
  if lvl > l then Printf.sprintf "(%s)" str
  else str


let rec pp_type ctx lvl tp =
  match Type.view tp with
  | TUnit  -> "Unit"
  | TEmpty -> "Empty"
  | TBool  -> "Bool"
  | TInt   -> "Int"
  | TUVar x ->
    begin match List.assq_opt x !ctx with
    | Some str -> str
    | None ->
      let name = Printf.sprintf "x%d" (List.length !ctx) in
      ctx := (x, name) :: !ctx;
      name
    end
  | TArrow(tp1, tp2) ->
    pp_at_level 0 lvl
      (Printf.sprintf "%s -> %s" (pp_type ctx 1 tp1) (pp_type ctx 0 tp2))
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

(* ========================================================================= *)
(* Unification *)

exception Cannot_unify

let rec contains_uvar x tp =
  let rec list_contains_uvar = function
    | [] -> false
    | tp :: tps -> contains_uvar x tp || list_contains_uvar tps
  in
  match Type.view tp with
  | TUVar y -> x == y
  | TUnit | TEmpty | TBool | TInt -> false
  | TArrow(tp1, tp2) ->
    contains_uvar x tp1 || contains_uvar x tp2
  | TProd(tps) | TCoProd(tps) ->
    list_contains_uvar tps


let unify_with_uvar x tp =
  if contains_uvar x tp then raise Cannot_unify
  else Type.set_uvar x tp

let rec unify tp1 tp2 =
  match Type.view tp1, Type.view tp2 with
  | TUVar x, TUVar y when x == y -> ()
  | TUVar x, _ -> unify_with_uvar x tp2
  | _, TUVar x -> unify_with_uvar x tp1

  | TUnit, TUnit -> ()
  | TUnit, _ -> raise Cannot_unify

  | TEmpty, TEmpty -> ()
  | TEmpty, _ -> raise Cannot_unify

  | TBool, TBool -> ()
  | TBool, _ -> raise Cannot_unify

  | TInt, TInt -> ()
  | TInt, _ -> raise Cannot_unify

  | TArrow(ta1, tb1), TArrow(ta2, tb2) ->
    unify ta1 ta2;
    unify tb1 tb2
  | TArrow _, _ -> raise Cannot_unify

  | TProd(ts1), TProd(ts2)
  | TCoProd(ts1), TCoProd(ts2) ->
    List.iter2 unify ts1 ts2
  | TCoProd _, _
  | TProd _, _ -> raise Cannot_unify

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
      let new_tp = Type.fresh_uvar () in
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
