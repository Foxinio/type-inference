open Core.Imast
open Utils
open Core

open Type

(* ========================================================================= *)
(* Unification *)

exception Cannot_unify

let contains_uvar env x tp =
  let helper default init t =
    match Type.view t with
    | TUVar y -> Type.uvar_compare x y = 0
    | _ -> default init t
  in Type.foldl helper false tp

let unify_with_uvar env x tp =
  if contains_uvar env x tp then raise Cannot_unify
  else Type.set_uvar x tp

let rec equal ?(env=Env.empty) tp1 tp2 =
  match Type.view tp1, Type.view tp2 with
  | TUVar (x), TUVar (y) when x == y -> ()

  | _, TUVar (x) -> unify_with_uvar env x tp1
  | TUVar (x), _ -> unify_with_uvar env x tp2

  | TADT (x, lvl1, tps1), TADT (y, lvl2, tps2)
      when IMAstVar.compare x y = 0 -> 
    assert(lvl1=lvl2);
    List.iter2 equal tps1 tps2
  | TADT _, _-> raise Cannot_unify

  | TVar x, TVar y when Type.TVar.compare x y = 0 -> ()
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
    equal ta1 ta2;
    equal tb1 tb2
  | TArrow _, _ -> raise Cannot_unify

  | TPair(tp1a, tp1b), TPair(tp2a, tp2b) ->
    equal tp1a tp2a;
    equal tp1b tp2b
  | TPair _, _ -> raise Cannot_unify
