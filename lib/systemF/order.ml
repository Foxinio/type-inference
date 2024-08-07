(** Type equality *)

open Main
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

  | TArrow(arr1, ta1, tb1), TArrow(arr2, ta2, tb2) 
      when Arrow.equal_uvar arr1 arr2  ->
    type_equal ta1 ta2 && type_equal tb1 tb2
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

  | TPair (tp1a, tp1b), TPair (tp2a, tp2b) ->
    type_equal tp1a tp2a && type_equal tp1b tp2b
  | TPair _, _ -> false

  | TADT (a1, tps1), TADT (a2, tps2) when var_compare a1 a2 = 0 ->
    List.for_all2 type_equal tps1 tps2
  | TADT _, _ -> false

let rec subtype arrow_compare tp1 tp2 =
  match tp1, tp2 with
  | TArrow(arr1, ta1, tb1), TArrow(arr2, ta2, tb2) 
      when arrow_compare arr1 arr2 ->
    subtype arrow_compare ta2 ta1 && subtype arrow_compare tb1 tb2
  | TArrow _, _ -> false

  | TForallT(a1, tp1), TForallT(a2, tp2) ->
    let lst = Seq.forever (fun () -> TVar(TVar.fresh ()))
      |> Seq.take (List.length a1)
      |> List.of_seq in
    begin try
        subtype arrow_compare (subst_list tp1 a1 lst) (subst_list tp2 a2 lst)
      with Invalid_argument _ -> false
    end
  | TForallT _, _ -> false

  | TPair (tp1a, tp1b), TPair (tp2a, tp2b) ->
    subtype arrow_compare tp1a tp2a && subtype arrow_compare tp1b tp2b
  | TPair _, _ -> false

  | (TUnit | TEmpty | TBool | TInt | TVar _  | TADT (_, _)), _ ->
    type_equal tp1 tp2



let fold_equal_subtype tp1 tp2 =
  let arr_compare arr1 arr2 =
    Arrow.subtype_uvar arr1 arr2
    && Arrow.view_fold arr1 = Arrow.view_fold arr2
  in subtype arr_compare tp1 tp2
let subtype = subtype Arrow.subtype_uvar
let supertype tp1 tp2 = subtype tp2 tp1

