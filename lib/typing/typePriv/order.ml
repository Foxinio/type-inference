open Main
open Core.Imast

let rec equal t1 t2 = match t1, t2 with
  | TUVar x, _ ->
    equal_with_uvar x t2
  | _, TUVar x ->
    equal_with_uvar x t1

  | TUnit, TUnit -> true
  | TUnit, _ -> false

  | TEmpty, TEmpty -> true
  | TEmpty, _ -> false

  | TVar x, TVar y when x = y -> true
  | TVar _, _ -> false

  | TADT (new_adt, new_lvl, new_tps),
    TADT (cur_adt, cur_lvl, cur_tps)
      when IMAstVar.compare new_adt cur_adt = 0
      && List.equal equal new_tps cur_tps ->
      assert (cur_lvl = new_lvl);
      true
  | TADT _, _ -> false

  | TBool, TBool -> true
  | TBool, _ -> false
  | TInt, TInt -> true
  | TInt, _ -> false

  | TArrow (targa, tresa),
    TArrow (targb, tresb) ->
    equal tresa tresb
    && equal targa targb
  | TArrow _, _ -> false

  | TPair(tp1a, tp1b), TPair(tp2a, tp2b) ->
      equal tp1a tp2a && equal tp1b tp2b
  | TPair _, _ -> false

and equal_with_uvar x tp =
  match !x, tp with
  | {value=Unrealised _;_}, _ ->
    true
  | {value=Realised tp2;_}, tp1 ->
    equal tp1 tp2
