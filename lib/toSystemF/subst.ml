open Core
open Typing

let get_subst template instance =
  let open Type in
  let rec inner mapping template instance =
    match view template, view instance with
    | (TUVar _ | TGVar _), _
    | _, (TUVar _ | TGVar _) ->
    failwith "Unification variable unrealized"
    | TUnit, TUnit | TBool, TBool | TInt, TInt | TEmpty, TEmpty -> mapping
    | TVar a, _ ->
      begin match TVarMap.find_opt a mapping with
      | Some tp when Equal.type_equal tp instance -> mapping
      | None -> TVarMap.add a instance mapping
      | Some _ -> failwith "internal error"
    end
    | TArrow (tps1, tp1), TArrow (tps2, tp2) ->
      inner (List.fold_left2 inner mapping tps1 tps2) tp1 tp2
    | TProd tps1, TProd tps2 ->
      List.fold_left2 inner mapping tps1 tps2
    | TADT (a1, _, tps1), TADT (a2, _, tps2) when Imast.IMAstVar.compare a1 a2 = 0 ->
      List.fold_left2 inner mapping tps1 tps2
    | (TUnit | TBool | TInt | TEmpty | TArrow _ | TProd _ | TADT _), _ ->
      failwith "internal error"
  in
  inner TVarMap.empty template instance
    |> TVarMap.to_list



