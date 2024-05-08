(** Type equality *)

open Type
open Subst

let rec type_equal tp1 tp2 =
  match tp1, tp2 with
  | TUnit, TUnit -> true
  | TUnit, _ -> false

  | TEmpty, TEmpty -> true
  | TEmpty, _ -> false

  | TBool, TBool -> true
  | TBool, _ -> false

  | TInt, TInt -> true
  | TInt, _ -> false

  | TVar x, TVar y -> TVar.compare x y = 0
  | TVar _, _ -> false

  | TArrow(ta1, tb1), TArrow(ta2, tb2) ->
    List.for_all2 type_equal ta1 ta2 && type_equal tb1 tb2
  | TArrow _, _ -> false

  | TForallT(a1, tp1), TForallT(a2, tp2) ->
    let lst = Seq.forever (fun () -> TVar(TVar.fresh ()))
      |> Seq.take (List.length a1)
      |> List.of_seq in
    begin try
        type_equal (subst_list tp1 a1 lst) (subst_list tp2 a2 lst)
      with Invalid_argument _ -> false
    end
  | TForallT _, _ -> false

  | TProd tps1, TProd tps2 ->
    List.for_all2 type_equal tps1 tps2
  | TProd _, _ -> false

  | TADT (a1, tps1), TADT (a2, tps2) when var_compare a1 a2 = 0 ->
    List.for_all2 type_equal tps1 tps2
  | TADT _, _ -> false

