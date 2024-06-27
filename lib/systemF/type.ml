(* System F Type and Expr definitions *)

open Core
open Imast


module TVar = Tvar.Make()

let var_compare = IMAstVar.compare

type adtvar = IMAstVar.t
type tvar = TVar.t
type var  = IMAstVar.t
type name = IMAstVar.t

type tp =
  | TUnit
  | TEmpty
  | TBool
  | TInt
  | TVar     of tvar
  | TArrow   of Effect.t * tp list * tp
  | TADT     of adtvar * tp list
  | TForallT of tvar list * tp
  | TPair    of tp * tp

type coersion =
  (* should arrows be contravariant?
   * TODO: think of an example *)
  | CId        of tp
  | CBot       of tp
  | CArrow     of Effect.t * coersion list * coersion
  | CForallT   of tvar list * coersion
  | CPair      of coersion * coersion
  | CMrgArrow  of coersion list * coersion
  | CSpltArrow of coersion list * coersion
  | CImprArrow of coersion

type expr =
  | EUnit
  | EBool   of bool
  | ENum    of int
  | EVar    of var
  | ECoerse of coersion * expr
  | EFn     of (var * tp) list * expr
  | EFix    of var * (var * tp) list * tp * expr
  | EApp    of expr * expr list
  (* Big lambda: Λα.τ *)
  | ETFn    of tvar list * expr
  (* Type Application: τ* *)
  | ETApp   of expr * tp list
  | ELet    of var * expr * expr
  | EExtern of string * tp * tp
  | EPair   of expr * expr
  | EFst    of expr
  | ESnd    of expr
  | EIf     of expr * expr * expr
  | ESeq    of expr * expr
  | EType   of name * tvar list * ctor_def list * expr
  | ECtor   of name * expr

  (* tp is type of `match expr with clauses` *)
  | EMatch  of expr * clause list * tp


and ctor_def = name * tp
and alias = name * tvar list
and clause = name * var * expr

type program = expr * string Imast.VarTbl.t

module VarMap  = IMAstVar.MakeMap()
module TVarMap = Map.Make(TVar)
module TVarSet = Set.Make(TVar)

module Coerse = struct
  let is_id = function CId _ -> true | _ -> false
  let unwrap_id = function CId tp -> Some tp | _ -> None

  let rec rebuild = function
    | CId tp -> tp, tp
    | CBot tp -> TEmpty, tp
    | CArrow (eff, cps, c) ->
      let tps1, tps2 = List.split @@ List.map rebuild cps in
      let tpres1, tpres2 = rebuild c in
      TArrow (eff, tps1, tpres1), TArrow (eff, tps2, tpres2)
    | CForallT (vars, c) ->
      let tp1, tp2 = rebuild c in
      TForallT (vars, tp1), TForallT (vars, tp2)
    | CPair (c1, c2) ->
      let tp1a, tp2a = rebuild c1 in
      let tp1b, tp2b = rebuild c2 in
      TPair (tp1a, tp1b), TPair (tp2a, tp2b)
    | CMrgArrow (cps, c) ->
      let tps1, tps2 = List.split @@ List.map rebuild cps in
      begin match rebuild c with
      | tpres1, TArrow(eff, tps2', tpres2) ->
        TArrow (Pure, tps1, tpres1),
        TArrow (eff, tps2 @ tps2', tpres2)
      | _ -> assert false
      end
    | CSpltArrow (cps, c) ->
      let tps1, tps2 = List.split @@ List.map rebuild cps in
      begin match rebuild c with
      | TArrow(eff, tps1', tpres1), tpres2 ->
        TArrow (eff, tps1 @ tps1', tpres1),
        TArrow (Pure, tps2, tpres2)
      | _ -> assert false
      end
    | CImprArrow c ->
      begin match rebuild c with
      | TArrow(Pure, tps1, tpres1),
        TArrow(Pure, tps2, tpres2) ->
        TArrow (Pure, tps1, tpres1),
        TArrow (Impure, tps2, tpres2)
      | _ -> assert false
      end
end
