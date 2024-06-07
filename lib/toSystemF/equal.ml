open Core.Imast
open Typing
open Type


let rec type_equal tp1 tp2 = 
  match view tp1, view tp2 with
  | (TUVar _ | TGVar _), _
  | _, (TUVar _ | TGVar _) ->
    failwith "Unification variable unrealized"

  | TUnit, TUnit -> true
  | TUnit, _ -> false

  | TBool, TBool -> true
  | TBool, _ -> false

  | TInt, TInt -> true
  | TInt, _ -> false

  | TEmpty, TEmpty -> true
  | TEmpty, _ -> false

  | TVar a, TVar b when TVar.compare a b = 0 -> true
  | TVar _, _ -> false

  | TArrow (tps1, tp1), TArrow (tps2, tp2) ->
    type_equal tp1 tp2 && List.for_all2 type_equal tps1 tps2
  | TArrow _, _ -> false

  | TPair (tp1a, tp1b), TPair (tp2a, tp2b) ->
    type_equal tp1a tp2a && type_equal tp1b tp2b
  | TPair _, _ -> false

  | TADT (a1, _, tps1), TADT (a2, _, tps2) when IMAstVar.compare a1 a2 = 0 ->
    List.for_all2 type_equal tps1 tps2
  | TADT _, _ -> false

