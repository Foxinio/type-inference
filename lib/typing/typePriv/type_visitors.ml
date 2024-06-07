open Main
open Uvar

let rec iter f : t -> unit =
  let default t = match t with
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _
    | TIUVar ({contents={value=Unrealised _;_}}) -> ()
    | TIUVar ({contents={value=Realised tp;_}}) ->
      iter f tp
    | TIADT (_, _, tps) ->
       List.iter (iter f) tps
    | TIArrow (tps, tp) ->
      List.iter (iter f) tps;
      iter f tp
    | TIPair (tp1, tp2) ->
      iter f tp1;
      iter f tp2
  in
  f default

let rec fold_map f init =
  let default acc t = match t with
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _ | TIUVar ({contents={value=Unrealised _;_}}) -> acc, t
    | TIUVar ({contents={value=Realised tp;_}} as x) ->
      let acc, tp = fold_map f acc tp in
      set_uvar x tp;
      acc, TIUVar x
    | TIADT (name, lvl, tps) ->
      let acc, tps = List.fold_left_map (fold_map f) acc tps in
      acc, TIADT (name, lvl, tps)
    | TIArrow (tps, tp) ->
      let acc, tps = List.fold_left_map (fold_map f) acc tps in
      let acc, tp = fold_map f acc tp in
      acc, TIArrow (tps, tp)
    | TIPair (tp1, tp2) ->
      let acc, tp1 = fold_map f acc tp1 in
      let acc, tp2 = fold_map f acc tp2 in
      acc, TIPair (tp1, tp2)
  in
  f default init



let rec map f : t -> t =
  let default t = match t with
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _ | TIUVar ({contents={value=Unrealised _;_}}) -> t
    | TIUVar ({contents={value=Realised tp;_}} as x) ->
      set_uvar x (map f tp);
      TIUVar x
    | TIADT (name, lvl, tps) ->
      TIADT (name, lvl, List.map (map f) tps)
    | TIArrow (tps, tp) ->
      TIArrow (List.map (map f) tps, map f tp)
    | TIPair (tp1, tp2) ->
      TIPair (map f tp1, map f tp2)
  in
  f default

let rec foldl f init t =
  let rec default init t = match t with
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _ | TIUVar ({contents={value=Unrealised _;_}}) -> init
    | TIADT (_, _, tps) ->
      List.fold_left (foldl f) init tps
    | TIUVar ({contents={value=Realised tp;_}}) ->
      foldl f (f default init tp) tp
    | TIPair (tp1, tp2) ->
      let init = foldl f (f default init tp1) tp1 in
      let init = foldl f (f default init tp2) tp2 in
      init
    | TIArrow (tps, tp) ->
      List.fold_left (foldl f) (f default init tp) tps
  in
  foldl f (f default init t) t

