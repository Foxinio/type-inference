open Main
open Type_visitors
open Core.Imast

let rec view (tp : t) : view =
  match tp with
  | TUVar {contents={value=Realised tp;_}} ->
      view tp
  | TUVar ({contents={value=Unrealised _;_}} as x) ->
      TUVar x
  | _ -> tp

and prune_uvar = function
  | TUVar ({contents={ value=Realised tp;_}} as x) ->
    let shortened = prune_uvar tp in
    x := { !x with value=Realised shortened };
    shortened
  | tp -> tp
