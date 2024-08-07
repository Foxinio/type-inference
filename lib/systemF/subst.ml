(** Type substitution *)

open Main

let rec subst tsub tp =
  match tp with
  | TUnit | TEmpty | TBool | TInt -> tp
  | TVar x ->
    begin match TVarMap.find_opt x tsub with
    | None    -> tp
    | Some tp -> tp
    end
  | TArrow(arr, targ, tres) ->
    TArrow(arr, subst tsub targ, subst tsub tres)
  | TForallT(a, tp) ->
    let f tsub a =
      let b = TVar.fresh () in
      TVarMap.add a (TVar b) tsub, b
    in
    let tsub, b = List.fold_left_map f tsub a in
    TForallT(b, subst tsub tp)
  | TPair (tp1, tp2) ->
    TPair(subst tsub tp1, subst tsub tp2)
  | TADT(a, tps) ->
    TADT(a, List.map (subst tsub) tps)

let subst_type tp x s =
  subst (TVarMap.singleton x s) tp

let subst_list tp xs ys =
  let tsub = List.fold_left2
    (fun tsub x y -> TVarMap.add x y tsub) TVarMap.empty xs ys in
  subst tsub tp

let subst_mapping tp xs =
  let tsub = List.fold_left
    (fun tsub (x,tp) -> TVarMap.add x tp tsub) TVarMap.empty xs in
  subst tsub tp


