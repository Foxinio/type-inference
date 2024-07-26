open Main
open Uvar

let iter f : t -> unit =
  let rec default t = match t with
    | TUnit | TEmpty | TBool | TInt | TVar _
    | TUVar ({contents={value=Unrealised _;_}}) -> ()
    | TUVar ({contents={value=Realised tp;_}}) ->
      f default tp
    | TADT (_, _, tps) ->
       List.iter (f default) tps
    | TArrow (tps, tp) ->
      f default tps;
      f default tp
    | TPair (tp1, tp2) ->
      f default tp1;
      f default tp2
  in
  f default

let rec fold_map f init =
  let default acc t = match t with
    | TUnit | TEmpty | TBool | TInt | TVar _ | TUVar ({contents={value=Unrealised _;_}}) -> acc, t
    | TUVar {contents={value=Realised tp;_}} ->
      fold_map f acc tp
    | TADT (name, lvl, tps) ->
      let acc, tps = List.fold_left_map (fold_map f) acc tps in
      acc, TADT (name, lvl, tps)
    | TArrow (tps, tp) ->
      let acc, tps = fold_map f acc tps in
      let acc, tp = fold_map f acc tp in
      acc, TArrow (tps, tp)
    | TPair (tp1, tp2) ->
      let acc, tp1 = fold_map f acc tp1 in
      let acc, tp2 = fold_map f acc tp2 in
      acc, TPair (tp1, tp2)
  in
  f default init



let map f : t -> t =
  let rec default t =
    match t with
    | TUnit | TEmpty | TBool | TInt | TVar _ | TUVar ({contents={value=Unrealised _;_}}) -> t
    | TUVar {contents={value=Realised tp;_}} ->
      f default tp
    | TADT (name, lvl, tps) ->
      TADT (name, lvl, List.map (f default) tps)
    | TArrow (tps, tp) ->
      TArrow (f default tps, f default tp)
    | TPair (tp1, tp2) ->
      TPair (f default tp1, f default tp2)
  in
  f default

let foldl (f : ('a -> t -> 'a) -> 'a -> t -> 'a) (init : 'a) (tp : t) =
  let rec default init (tp : t) = match tp with
    | TUnit | TEmpty | TBool | TInt | TVar _ | TUVar ({contents={value=Unrealised _;_}}) -> init
    | TPair (tp1, tp2) ->
      let init = f default init tp1 in
      let init = f default init tp2 in
      init
    | TArrow (targ, tres) ->
      let init = f default init targ in
      let init = f default init tres in
      init
    | TADT (_, _, tps) ->
      List.fold_left (f default) init tps
    | TUVar ({contents={value=Realised tp;_}}) ->
      f default init tp
  in
  f default init tp

