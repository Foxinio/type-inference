open Main
open Type_visitors

let degeneralize_uvars tp =
  let rec helper default = function
    | TIUVar {contents={value=Realised tp;_}} -> helper default tp
    | TIUVar ({contents={value=Unrealised _;_}} as x) ->
      x := { !x with is_gvar=false };
      TIUVar x
    | tp -> default tp in
  map helper tp

let rec view tp =
  match tp with
  | TIUVar ({contents={is_gvar;_}} as x) when is_gvar ->
      TGVar (x, view_uvar x)
  | TIUVar ({contents={value=Realised _;_}} as x) ->
      Option.get (view_uvar x)
  | TIUVar ({contents={value=Unrealised _;_}} as x) ->
      TUVar x
  | TIVar x -> TVar x
  | TIADT (x, lvl, tps) -> TADT (x, lvl, tps)
  | TIUnit -> TUnit
  | TIEmpty -> TEmpty
  | TIBool -> TBool
  | TIInt -> TInt
  | TIArrow(tps, tp2) -> TArrow(tps, tp2)
  | TIProd tps -> TProd tps

and prune_uvar = function
  | TIUVar ({contents={ value=Realised tp;_}} as x) ->
    let shortened = prune_uvar tp in
    x := { !x with value=Realised shortened };
    shortened
  | tp -> tp

and view_uvar x =
  match !x with
  | {value=Unrealised _; _} -> None
  | {value=Realised tp; _ } ->
    let tp = prune_uvar tp in
    x := { !x with value=Realised tp };
    Some (view tp)
