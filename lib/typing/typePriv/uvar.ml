open Main
open Core.Imast

open Order

let makeUvar gvar level =
  { value=Unrealised level; id=UVar.fresh (); is_gvar=gvar; }

let fresh_uvar level = TIUVar (ref (makeUvar false level))
let fresh_gvar level = TIUVar (ref (makeUvar true level))

let uvar_compare { contents={id=id1;_}} { contents={id=id2;_}} = UVar.compare id1 id2

module UVarSet = Set.Make(struct
  type t = uvar
  let compare = uvar_compare
end)

let rec set_uvar x tp =
  begin match !x with
  | {value=Unrealised level; _} ->
    lower_uvar_level level x tp
  | _ -> ()
  end;
  match !x with
  | {value=Unrealised _; _} ->
    x := {!x with value=Realised tp }
  | {value=Realised tp_current; is_gvar=true;_} ->
      (* TODO: confirm that meet belongs here *)
      let res = merge tp tp_current in
      x := { !x with value=Realised res }
  | { value=Realised _;_ } ->
     failwith "tried to set realised uvar"

and lower_uvar_level level' x tp =
    let rec inner = function
      | TIUVar ({contents={ value=Unrealised level;_}} as x)
          when Level.compare level' level < 0 ->
        x := { !x with value=Unrealised level' };
      | TIADT (_, level, _) when Level.compare level level' > 0->
        raise (Cannot_compare (tp, (TIUVar x)))
      | TIUnit | TIEmpty | TIBool | TIInt | TIVar _
      | TIUVar ({contents={value=Unrealised _;_}}) -> ()
      | TIUVar ({contents={value=Realised tp;_}}) ->
        inner  tp
      | TIADT (_, _, tps) ->
         List.iter inner tps
      | TIArrow (_, tps, tp) ->
        List.iter inner tps;
        inner  tp
      | TIPair (tp1, tp2) ->
        inner tp1;
        inner tp2
    in inner tp

