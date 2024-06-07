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
    | TPair (tp1a, tp1b), TPair (tp2a, tp2b) ->
      let mapping = inner mapping tp1a tp2a in
      let mapping = inner mapping tp1b tp2b in
      mapping
    | TADT (a1, _, tps1), TADT (a2, _, tps2) when Imast.IMAstVar.compare a1 a2 = 0 ->
      List.fold_left2 inner mapping tps1 tps2
    | (TUnit | TBool | TInt | TEmpty | TArrow _ | TPair _ | TADT _), _ ->
      failwith "internal error"
  in
  inner TVarMap.empty template instance
    |> TVarMap.to_list



