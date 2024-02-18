(** Type inference (for simple types) *)

open Core.Ast
open Core

module TVar = Tvar.Make()
module type TVar_S = Tvar.TVar_S

(** Internal representation of types *)
module Type : sig

  module UVar : TVar_S

  type t
  type uvar
  type view =
    | TUnit
    | TEmpty
    | TBool
    | TInt
    | TVar    of t Ast.var
    | TGVar   of uvar * view option
    | TUVar   of uvar
    | TArrow  of t list * t
    | TProd   of t list
    | TCoProd of t list

  module UVarSet : Set.S with type elt = uvar
  module UVarMap : Map.S with type key = uvar

  val fresh_uvar : unit -> t
  val fresh_gvar : unit -> t

  val t_unit   : t
  val t_empty  : t
  val t_bool   : t
  val t_int    : t
  val t_var    : t Ast.var -> t
  val t_arrow  : t list -> t -> t
  val t_pair   : t -> t -> t
  val t_copair : t -> t -> t
  val t_prod   : t list -> t
  val t_coprod : t list -> t

  val view : t -> view

  val set_uvar : uvar -> t -> unit
  val set_gvar : uvar -> t -> unit
  val t_of_uvar : uvar -> t option
  val uvar_compare : uvar -> uvar -> int

  exception Cannot_compare of t * t


  type typ

  val instantiate : typ -> t
  val typ_mono : t -> typ
  val typ_schema : t -> UVarSet.t -> typ
  val generalize : UVarSet.t -> t -> typ

  val get_uvars : typ -> UVarSet.t

end = struct

  module UVar = TVar

  type t =
    | TIUnit
    | TIEmpty
    | TIBool
    | TIInt
    | TIVar    of t Ast.var
    | TIGVar   of uvar
    | TIUVar   of uvar
    | TIArrow  of t list * t
    | TIProd   of t list
    | TICoProd of t list

  and uvar = (t option * UVar.t) ref
  and view =
    | TUnit
    | TEmpty
    | TBool
    | TInt
    | TVar    of t Ast.var
    | TGVar   of uvar * view option
    | TUVar   of uvar
    | TArrow  of t list * t
    | TProd   of t list
    | TCoProd of t list

  let fresh_uvar () = TIUVar (ref (None, UVar.fresh ()))
  let fresh_gvar () = TIGVar (ref (None, UVar.fresh ()))

  let t_unit  = TIUnit
  let t_empty = TIEmpty
  let t_bool  = TIBool
  let t_int   = TIInt
  let t_var x = TIVar x
  let t_arrow  tps tp2 = TIArrow(tps, tp2)
  let t_pair   tp1 tp2 = TIProd([tp1; tp2])
  let t_copair tp1 tp2 = TICoProd([tp1; tp2])
  let t_prod   tps = TIProd(tps)
  let t_coprod tps = TICoProd(tps)

  let rec t_of_view = function
    | TUVar x -> TIUVar x
    | TGVar (x, _) -> TIGVar x
    | TVar x -> TIVar x
    | TUnit -> TIUnit
    | TEmpty -> TIEmpty
    | TBool -> TIBool
    | TInt -> TIInt
    | TArrow(tps, tp2) -> TIArrow(tps, tp2)
    | TProd tps -> TIProd tps
    | TCoProd tps -> TICoProd tps

  let rec view tp =
    let view_uvar x =
      match !x with
      | None, _ -> None
      | Some tp, i ->
        let tp = view tp in
        x := Some (t_of_view tp), i;
        Some tp
    in
    match tp with
    | TIUVar ({contents=Some(_),_} as x) ->
        Option.get (view_uvar x)
    | TIUVar ({contents=None,_} as x) ->
        TUVar x
    | TIGVar x ->
        TGVar (x, view_uvar x)
    | TIVar x -> TVar x
    | TIUnit -> TUnit
    | TIEmpty -> TEmpty
    | TIBool -> TBool
    | TIInt -> TInt
    | TIArrow(tps, tp2) -> TArrow(tps, tp2)
    | TIProd tps -> TProd tps
    | TICoProd tps -> TCoProd tps


  exception Cannot_compare of t * t

  let rec set_uvar_int x tp general =
    match !x with
    | None, i -> x := Some tp, i
    | Some tp_current, i when general ->
        let res = reconstruct tp tp_current in
        x := Some res, i
    | Some _, i -> assert false

  and reconstruct (new_tp : t) (currrnet_tp : t) =
    let rec reconstruct_arrows (tpsa, resa) (tpsb, resb) =
      match tpsa, tpsb with
      | tpa :: tpsa, tpb :: tpsb ->
          (* because arguments in arrows are contravariant these are reversed *)
          let tp = reconstruct tpb tpa in
          let rest, res = reconstruct_arrows (tpsa, resa) (tpsb, resb) in
          tp :: rest, res
      | [], _ :: _ ->
          [], reconstruct resa (TIArrow (tpsb, resb))
      | _ :: _, [] ->
          [], reconstruct (TIArrow (tpsa, resa)) resb
      | [], [] ->
          [], reconstruct resa resb
    in
    let uvar_map x tp fn =
      match !x with
      | None, i ->
          x := Some tp, i;
          tp
      | Some tp, i ->
          let res = fn tp in
          x := Some res, i;
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

    (* Here is a good design question, does this rule make sense *)
    | _, TIUnit    -> TIUnit

    | TIEmpty, TIEmpty -> TIEmpty
    | TIEmpty, _     -> TIEmpty

    | TIBool, TIBool -> TIBool
    | TIInt, TIInt -> TIInt

    | TIArrow (tpsa, tp_resa),
      TIArrow (tpsb, tp_resb) ->
        let args, res = reconstruct_arrows (tpsa, tp_resa) (tpsb, tp_resb) in
        t_arrow args res

    | TIProd(ts1), TIProd(ts2) when List.length ts1 = List.length ts2 ->
      TIProd (List.map2 reconstruct ts1 ts2)
    | TICoProd(ts1), TICoProd(ts2) when List.length ts1 = List.length ts2 ->
      TICoProd (List.map2 reconstruct ts1 ts2)
    | _, _ -> raise (Cannot_compare (new_tp, currrnet_tp))


  let set_uvar x tp =
    set_uvar_int x tp false
  let set_gvar x tp =
    set_uvar_int x tp true
  let t_of_uvar { contents=x,_ } = x
  let uvar_compare { contents=_,x } { contents=_,y } = UVar.compare x y

  module UVarSet = Set.Make(struct
    type t = uvar
    let compare = uvar_compare
  end)

  module UVarMap = Map.Make(struct
    type t = uvar
    let compare = uvar_compare
  end)



  type typ =
    | Mono of t
    | Schema of t * UVarSet.t

  let typ_mono t = Mono t
  let typ_schema t set = Schema (t, set)

  let instantiate = function
    | Mono tp -> tp
    | Schema (tp, uvars) ->
        let uvars_seq =
          UVarSet.to_seq uvars |>
          Seq.flat_map (fun x -> Seq.return (x, fresh_uvar ())) in
        let mapper = UVarMap.of_seq uvars_seq in
        let rec instantiate = function
          | TIUVar (x) ->
              UVarMap.find_opt x mapper |> Option.value ~default:(TIUVar x)
          | TIGVar (x) ->
              UVarMap.find_opt x mapper |> Option.value ~default:(TIGVar x)
          | TIArrow (tps, tp2) ->
              let tp1 = List.map instantiate tps in
              let tp2 = instantiate tp2 in
              TIArrow (tp1, tp2)
          | TIProd tps ->
              TIProd (List.map instantiate tps)
          | TICoProd tps ->
              TICoProd (List.map instantiate tps)
          | tp -> tp
        in instantiate tp

  let rec get_uvars_of_t set t =
    (* also this needs to be tested if its more effitient to build up set
     * by constantly creating new ones and merging them,
     * or create one list and turn it into set after everything *)
    let fold_fun acc tp = get_uvars_of_t set tp |> UVarSet.union acc in
    match view t with
    | TGVar (x, None)
    | TUVar (x)
        when UVarSet.find_opt x set |> Option.is_none -> UVarSet.singleton x
    | TUnit | TEmpty | TBool | TInt | TVar _ | TGVar (_, None) | TUVar _ -> UVarSet.empty
    | TGVar (_, Some tp) -> get_uvars_of_t set (t_of_view tp)
    | TArrow (tps, tp2) -> UVarSet.union (List.fold_left fold_fun UVarSet.empty tps) (get_uvars_of_t set tp2)
    | TProd tps
    | TCoProd tps ->
        List.fold_left fold_fun UVarSet.empty tps

    (* so im not sure what to do here whether or not
     * uvars representing polymorphic variables should be returned as part of uvarset
     * because on the one hand they are not really free uvars in this type
     * because they are not considered uvars anymore
     * on the other hand because of how they are chosen they shouldn't be visible from outsite
     * and also if given they would only be subtracted so this wouldn't break anything. *)
  let get_uvars t =
    match t with
    | Mono t -> get_uvars_of_t UVarSet.empty t
    | Schema (tp, uvars) ->
        get_uvars_of_t uvars tp

  let generalize env_uvars tp =
    let tp_uvars  = get_uvars_of_t UVarSet.empty tp in
    let diff = UVarSet.diff tp_uvars env_uvars in
    typ_schema tp diff


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
    | TVar x -> "rec_x"
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
    | TArrow(tps, tp2) ->
      pp_at_level 0 lvl
        (Printf.sprintf "%s -> %s" (pp_list "," ctx 1 tps) (pp_type ctx 0 tp2))
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
    | TUVar (y) -> x == y
    | TGVar (_, Some tp) -> contains_uvar_int tp
    | TUnit | TEmpty | TBool | TInt | TGVar (_, None) | TVar _ -> false
    | TArrow(tp1, tp2) ->
      list_contains_uvar tp1 || contains_uvar x tp2
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
    | TUVar (x), TUVar (y)
    | TGVar (x, None), TGVar (y, None) when x == y -> ()

    | _, TUVar (x) -> unify_with_uvar x tp1
    | TUVar (x), _ -> unify_with_uvar x tp2

    | _, TGVar (x, None) -> unify_with_uvar x tp1
    | TGVar (x, None), _ -> unify_with_uvar x tp2

    | TGVar (x, Some(TArrow _)), TArrow _ ->
        unify_with_uvar x tp2
    | TArrow _, TGVar (x, Some(TArrow _)) ->
        unify_with_uvar x tp1

    | TGVar (_, Some tp1), tp2 -> unify_int tp1 tp2
    | tp1, TGVar (_, Some tp2) -> unify_int tp1 tp2

    | TVar x, TVar y when x = y -> ()
    | TVar _, _ -> raise Cannot_unify

    | TUnit, TUnit -> ()
    | TUnit, _ -> raise Cannot_unify

    | TEmpty, TEmpty -> ()
    | TEmpty, _ -> raise Cannot_unify

    | TBool, TBool -> ()
    | TBool, _ -> raise Cannot_unify

    | TInt, TInt -> ()
    | TInt, _ -> raise Cannot_unify

    | TArrow(ta1, tb1), TArrow(ta2, tb2) ->
      List.iter2 unify ta1 ta2;
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
  module VarMap : Map.S with type key = string

  (** this is gonna be removed but is kept for now to make it compile *)
  val empty : t
  val of_var_names : Type.t Ast.var VarMap.t -> t

  val extend_gamma : t -> Type.t Ast.var -> Type.typ -> t
  val lookup_gamma : t -> Type.t Ast.var -> Type.typ option

  val extend_delta : t -> Ast.ctor_name list -> Type.t Ast.var -> t
  val lookup_delta : t -> Ast.ctor_name -> Type.t Ast.var option

  val get_uvars : t -> UVarSet.t
end = struct
  module VarMap = Map.Make(String)

  type t = {
    gamma: Type.typ VarMap.t;
    delta: Type.t Ast.var VarMap.t;
    var_name: Type.t Ast.var VarMap.t
  }

  let empty = {
    gamma=VarMap.empty;
    delta=VarMap.empty;
    var_name=VarMap.empty
  }
  let of_var_names var_name =
    { empty with var_name }

  let extend_gamma ({ gamma;  _} as env) (x,_) tp =
    { env with
      gamma=VarMap.add x tp gamma;
    }

  let lookup_gamma {gamma;_} (x,_) =
    VarMap.find_opt x gamma

  let get_uvars {gamma;_} =
    VarMap.fold (fun _name typ acc ->
      Type.get_uvars typ |> UVarSet.union acc) gamma UVarSet.empty


  let extend_delta ({delta;_} as env) ctor_lst x =
    { env with delta =
      VarMap.add_seq
        (List.to_seq ctor_lst |> Seq.flat_map (fun ctor -> Seq.return (ctor, x)))
        delta
    }

  let lookup_delta {delta;_} ctor = VarMap.find_opt ctor delta
end

let rec infer_type env (e : Type.t Ast.expr) =
  let extend_list xs env =
    let extend (tps, env) x =
      let new_tp = Type.fresh_gvar () in
      new_tp :: tps, Env.extend_gamma env x (Type.typ_mono new_tp)
    in
    List.fold_left extend ([], env) xs
  in
  match e.data with
  | EUnit   -> Type.t_unit
  | EBool _ -> Type.t_bool
  | ENum  _ -> Type.t_int
  | EVar  ((name,_) as x) ->
    begin match Env.lookup_gamma env x with
    | Some tp -> Type.instantiate tp
    | None ->
      Utils.report_error e "Unbound variable %s" name
    end
  | EFn(xs, body) ->
    let tps, env = extend_list xs env in
    let tp2 = infer_type env body in
    Type.t_arrow tps tp2
  | EFix(f, xs, body) ->
    let tps, env = extend_list xs env in
    let tp2 = Type.fresh_uvar () in
    let f_tp = Type.t_arrow tps tp2 in
    check_type (Env.extend_gamma env f (Type.typ_mono f_tp)) body tp2;
    f_tp
  | EApp(e1, es) ->
    let generate _ = Type.fresh_uvar () in
    let tps = List.map generate es in
    let tp1 = Type.fresh_uvar () in
    check_type env e1 (Type.t_arrow tps tp1);
    List.iter2 (fun e tp -> check_type env e tp) es tps;
    tp1
  | ELet(x, e1, e2) ->
    let tp = infer_type env e1 in
    let tp = Type.generalize (Env.get_uvars env) tp in
    infer_type (Env.extend_gamma env x tp) e2
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
    let tp = Type.fresh_uvar () in
    check_type env e (Type.t_copair tp1 tp2);
    check_type (Env.extend_gamma env x1 (Type.typ_mono tp1)) e1 tp;
    check_type (Env.extend_gamma env x2 (Type.typ_mono tp2)) e2 tp;
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
  | EType _ | ECtor _ | EMatch _ ->
    (* TODO: not implemented *)
    Utils.report_error e "This language feature is not supported yet!"

and check_type env (e : Type.t Ast.expr) tp =
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
