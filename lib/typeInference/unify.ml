open Core.Imast
open Core

open Type

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
    | TScheme (_, tps)
    | TProd(tps) ->
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

    | TScheme (x, tps1), TScheme (y, tps2) when IMAstVar.compare x y = 0 -> 
      List.iter2 unify tps1 tps2
    | TScheme _, _-> raise Cannot_unify

    | TVar x, TVar y when IMAstVar.compare x y = 0 -> ()
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

    | TProd(ts1), TProd(ts2) ->
      List.iter2 unify ts1 ts2
    | TProd _, _ -> raise Cannot_unify
  in
  unify_int (Type.view tp1) (Type.view tp2)

