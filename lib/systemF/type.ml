(* System F Type and Expr definitions *)

open Core
open Imast

type ('a,'b) node = {
  data  : 'a;
  extra : 'b;
}


module TVar = Var.Make()

module Label = Var.Make()
module TypeLabel = Var.Make()

let var_compare = IMAstVar.compare

type adtvar = IMAstVar.t
type tvar = TVar.t
type var  = IMAstVar.t
type name = IMAstVar.t

type 'extra tp = ('extra tp_data, 'extra) node
and 'extra tp_data =
  | TUnit
  | TEmpty
  | TBool
  | TInt
  | TVar     of tvar
  | TArrow   of Effect.uvar * Folding.uvar * 'extra tp list * 'extra tp
  | TADT     of adtvar * 'extra tp list
  | TForallT of tvar list * 'extra tp
  | TPair    of 'extra tp * 'extra tp

type coersion =
  (* should arrows be contravariant?
   * TODO: think of an example *)
  | CId        of unit tp
  | CBot       of unit tp

  (* CPureArrow *)
  | CPArrow     of coersion list * coersion
  | CForallT   of tvar list * coersion
  | CPair      of coersion * coersion

  (* three below expect CPArrow or one of the other to be underneath *)
  | CMrgArrow  of coersion
  | CSpltArrow of coersion
  | CImprArrow of coersion

type nonrec tp = TypeLabel.t tp
let make_tp tp = { data=tp; extra=TypeLabel.fresh () }
let rec refresh_tp tp =
  match tp.data with
  | TUnit -> make_tp TUnit
  | TEmpty -> make_tp TEmpty
  | TBool -> make_tp TBool
  | TInt -> make_tp TInt
  | TVar var -> make_tp (TVar var)
  | TArrow (eff, fold, args, res) ->
    let args = List.map refresh_tp args in
    let res = refresh_tp res in
    make_tp (TArrow (eff, fold, args, res))
  | TADT (var, args) ->
    let args = List.map refresh_tp args in
    make_tp (TADT (var, args))
  | TForallT (vars, tp) ->
    let tp = refresh_tp tp in
    make_tp (TForallT (vars, tp))
  | TPair (tp1, tp2) ->
    let tp1 = refresh_tp tp1 in
    let tp2 = refresh_tp tp2 in
    make_tp (TPair (tp1, tp2))


type 'extra expr = ('extra expr_data, 'extra) node
and 'extra expr_data =
  | EUnit
  | EBool   of bool
  | ENum    of int
  | EVar    of var
  | ECoerse of coersion * 'extra expr
  | EFn     of (var * tp) list * 'extra expr
  | EFix    of var * (var * tp) list * tp * 'extra expr
  | EApp    of 'extra expr * 'extra expr list
  (* Big lambda: Λα.τ *)
  | ETFn    of tvar list * 'extra expr
  (* Type Application: τ* *)
  | ETApp   of 'extra expr * tp list
  | ELet    of var * 'extra expr * 'extra expr
  | EExtern of string * tp * tp
  | EPair   of 'extra expr * 'extra expr
  | EFst    of 'extra expr
  | ESnd    of 'extra expr
  | EIf     of 'extra expr * 'extra expr * 'extra expr
  | ESeq    of 'extra expr * 'extra expr
  | EType   of name * tvar list * ctor_def list * 'extra expr
  | ECtor   of name * 'extra expr

  (* tp is type of `match 'extra expr with clauses` *)
  | EMatch  of 'extra expr * 'extra clause list * tp


and ctor_def = name * tp
and alias = name * tvar list
and 'extra clause = name * var * 'extra expr

(* ------------------------------------------------------------------------- *)

type program = Label.t expr * string Imast.VarTbl.t
let make data = { data; extra = Label.fresh () }
let get_data { data; _ } = data
let get_extra { extra; _ } = extra

(* ------------------------------------------------------------------------- *)

module VarMap  = IMAstVar.MakeMap()
module TVarMap = Map.Make(TVar)
module TVarSet = Set.Make(TVar)

let impure_arr = function
  | TArrow (eff, _, _, _)  -> Effect.impure_uvar eff
  | _ -> assert false

let split_arr = function
  | TArrow (eff, fold, _, _) ->
    if Effect.uvar_is_impure eff
    then failwith "trying to split impure arrow"
    else Folding.split fold
  | _ -> assert false

let merge_arr = function
  | TArrow (_, fold, _, _) -> Folding.merge fold
  | _ -> assert false

module Coerse = struct
  let is_id = function CId _ -> true | _ -> false
  let unwrap_id = function CId tp -> Some tp | _ -> None

  let rec rebuild : coersion -> tp * tp = function
    | CId tp -> refresh_tp tp, refresh_tp tp
    | CBot tp -> make_tp TEmpty, refresh_tp tp
    | CPArrow (cps, c) ->
      let tps1, tps2 = List.split @@ List.map rebuild cps in
      let tpres1, tpres2 = rebuild c in
      make_tp (TArrow (Effect.fresh_uvar (), Folding.fresh (), tps1, tpres1)),
      make_tp (TArrow (Effect.fresh_uvar (), Folding.fresh (), tps2, tpres2))
    | CForallT (vars, c) ->
      let tp1, tp2 = rebuild c in
      make_tp (TForallT (vars, tp1)), make_tp (TForallT (vars, tp2))
    | CPair (c1, c2) ->
      let tp1a, tp2a = rebuild c1 in
      let tp1b, tp2b = rebuild c2 in
      make_tp (TPair (tp1a, tp1b)), make_tp (TPair (tp2a, tp2b))
    | CMrgArrow c ->
      let (_, tp2) as res = rebuild c in
      merge_arr tp2;
      res
    | CSpltArrow c ->
      let (_, tp2) as res = rebuild c in
      split_arr tp2;
      res
    | CImprArrow c ->
      let (_, tp2) as res = rebuild c in
      impure_arr tp2;
      res
end
