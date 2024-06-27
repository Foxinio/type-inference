(** Type substitution *)

open Type

let rec subst tsub tp =
  match tp with
  | TUnit | TEmpty | TBool | TInt -> tp
  | TVar x ->
    begin match TVarMap.find_opt x tsub with
    | None    -> tp
    | Some tp -> tp
    end
  | TArrow(eff, tps, tp2) ->
    TArrow(eff, List.map (subst tsub) tps, subst tsub tp2)
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
  let tsub = List.fold_left2 (fun tsub x y -> TVarMap.add x y tsub) TVarMap.empty xs ys in
  subst tsub tp

let subst_mapping tp xs =
  let tsub = List.fold_left (fun tsub (x,tp) -> TVarMap.add x tp tsub) TVarMap.empty xs in
  subst tsub tp


let get_subst env_bound_tvars template instance =
  let open Type in
  let rec inner bounded mapping template instance =
    match template, instance with
    | TUnit, TUnit | TBool, TBool | TInt, TInt | TEmpty, TEmpty -> mapping
    | TVar a, _ ->
      if TVarSet.mem a bounded then
        begin match TVarMap.find_opt a mapping with
        | None -> TVarMap.add a instance mapping
        | Some _ -> failwith "internal error"
        end
      else mapping
    | TForallT (a, tp1), TForallT (b, tp2) ->
      let bounded = List.fold_left (Fun.flip TVarSet.add) bounded a in
      inner bounded mapping tp1 tp2
    | TArrow (eff1, tps1, tp1), TArrow (eff2, tps2, tp2) when eff1 = eff2 ->
      inner bounded (List.fold_left2 (inner bounded) mapping tps1 tps2) tp1 tp2
    | TPair (tp1a, tp1b), TPair (tp2a, tp2b) ->
      let mapping = inner bounded mapping tp1a tp2a in
      let mapping = inner bounded mapping tp1b tp2b in
      mapping
    | TADT (a1, tps1), TADT (a2, tps2) when Core.Imast.IMAstVar.compare a1 a2 = 0 ->
      List.fold_left2 (inner bounded) mapping tps1 tps2
    | (TUnit | TBool | TInt | TEmpty | TArrow _ | TPair _ | TADT _ | TForallT _ ), _ ->
      failwith "internal error"
  in
  inner env_bound_tvars TVarMap.empty template instance
    |> TVarMap.to_list


