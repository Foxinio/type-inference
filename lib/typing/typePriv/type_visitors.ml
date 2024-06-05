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
    | TIProd tps ->
      List.iter (iter f) tps
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
    | TIProd tps ->
      let acc, tps = List.fold_left_map (fold_map f) acc tps in
      acc, TIProd tps
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
    | TIProd tps ->
      TIProd (List.map (map f) tps)
  in
  f default


let rec foldr f t init =
  let rec default init t = match t with
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _ | TIUVar ({contents={value=Unrealised _;_}}) -> init
    | TIADT (_, _, tps) ->
      List.fold_right (foldr f) tps init
    | TIUVar ({contents={value=Realised tp;_}}) ->
      f default (foldr f tp init) tp
    | TIProd tps ->
      List.fold_right (foldr f) tps init
    | TIArrow (tps, tp) ->
      f default (List.fold_right (foldr f) tps init) tp
  in
  f default (foldr f t init) t

let rec foldl f init t =
  let rec default init t = match t with
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _ | TIUVar ({contents={value=Unrealised _;_}}) -> init
    | TIADT (_, _, tps) ->
      List.fold_left (foldl f) init tps
    | TIUVar ({contents={value=Realised tp;_}}) ->
      foldl f (f default init tp) tp
    | TIProd tps ->
      List.fold_left (foldl f) init tps
    | TIArrow (tps, tp) ->
      List.fold_left (foldl f) (f default init tp) tps
  in
  foldl f (f default init t) t

