open Main
open Uvar

let rec iter f : t -> unit =
  let default t = match t with
    | TUnit | TEmpty | TBool | TInt | TVar _
    | TUVar ({contents={value=Unrealised _;_}}) -> ()
    | TUVar ({contents={value=Realised tp;_}}) ->
      iter f tp
    | TADT (_, _, tps) ->
       List.iter (iter f) tps
    | TArrow (_, tps, tp) ->
      iter f tps;
      iter f tp
    | TPair (tp1, tp2) ->
      iter f tp1;
      iter f tp2
  in
  f default

let rec fold_map f init =
  let default acc t = match t with
    | TUnit | TEmpty | TBool | TInt | TVar _ | TUVar ({contents={value=Unrealised _;_}}) -> acc, t
    | TUVar ({contents={value=Realised tp;_}} as x) ->
      let acc, tp = fold_map f acc tp in
      set_uvar x tp;
      acc, TUVar x
    | TADT (name, lvl, tps) ->
      let acc, tps = List.fold_left_map (fold_map f) acc tps in
      acc, TADT (name, lvl, tps)
    | TArrow (eff, tps, tp) ->
      let acc, tps = fold_map f acc tps in
      let acc, tp = fold_map f acc tp in
      acc, TArrow (eff, tps, tp)
    | TPair (tp1, tp2) ->
      let acc, tp1 = fold_map f acc tp1 in
      let acc, tp2 = fold_map f acc tp2 in
      acc, TPair (tp1, tp2)
  in
  f default init



let rec map f : t -> t =
  let default t = match t with
    | TUnit | TEmpty | TBool | TInt | TVar _ | TUVar ({contents={value=Unrealised _;_}}) -> t
    | TUVar ({contents={value=Realised tp;_}} as x) ->
      set_uvar x (map f tp);
      TUVar x
    | TADT (name, lvl, tps) ->
      TADT (name, lvl, List.map (map f) tps)
    | TArrow (eff, tps, tp) ->
      TArrow (eff, map f tps, map f tp)
    | TPair (tp1, tp2) ->
      TPair (map f tp1, map f tp2)
  in
  f default

let rec foldl f init t =
  let rec default init t = match t with
    | TUnit | TEmpty | TBool | TInt | TVar _ | TUVar ({contents={value=Unrealised _;_}}) -> init
    | TADT (_, _, tps) ->
      List.fold_left (foldl f) init tps
    | TUVar ({contents={value=Realised tp;_}}) ->
      foldl f (f default init tp) tp
    | TPair (tp1, tp2) ->
      let init = foldl f (f default init tp1) tp1 in
      let init = foldl f (f default init tp2) tp2 in
      init
    | TArrow (_, tps, tp) ->
      foldl f (f default init tp) tps
  in
  foldl f (f default init t) t

