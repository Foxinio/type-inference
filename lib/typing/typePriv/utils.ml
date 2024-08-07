open Main
open Type_visitors
open Core.Imast
open Core.Utils
open Uvar

(* visited Set.t is not needed sanity check,
    uvars are prevented from forming cycles
    by checking `contains_uvar` before setting them *)
let rec view visited (tp : t) : view =
  match tp with
  | TUVar ({contents={value=Realised tp1;_}} as x) ->
      assert (UVarSet.mem x visited |> not);
      let visited = UVarSet.add x visited in
      x := { !x with value=Realised (prune_uvar visited tp1) };
      view visited tp1
  | TUVar ({contents={value=Unrealised _;_}} as x) ->
      TUVar x
  | _ ->
    tp

and prune_uvar visited = function
  | TUVar ({contents={ value=Realised tp;_}} as x) ->
    assert (UVarSet.mem x visited |> not);
    let visited = UVarSet.add x visited in
    let shortened = prune_uvar visited tp in
    x := { !x with value=Realised shortened };
    shortened
  | tp -> tp

let view tp = view UVarSet.empty tp
