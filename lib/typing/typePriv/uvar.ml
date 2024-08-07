open Main

let makeUvar gvar level =
  { value=Unrealised level; id=UVar.fresh (); }

let string_of_uvar uv = match !uv with
  | {value=Unrealised lvl; id } ->
    "["^Level.to_string lvl^","^UVar.to_string id^"]"
  | {value=Realised _; id } -> "[id="^UVar.to_string id^"]"

let fresh_uvar level =
  TUVar (ref (makeUvar false level))

let uvar_compare { contents={id=id1;_}} { contents={id=id2;_}} =
  UVar.compare id1 id2

module UVarSet = Set.Make(struct
  type t = uvar
  let compare = uvar_compare
end)

let rec set_uvar x tp =
  match !x with
  | {value=Unrealised level; _} ->
    lower_uvar_level level x tp;
    x := {!x with value=Realised tp }
  | { value=Realised _;_ } ->
    Core.Utils.report_internal_error "Tried to set realised uvar"

and lower_uvar_level level' x (tp : t) =
    let rec inner = function
      | TUVar ({contents={ value=Unrealised level;_}} as x)
          when Level.compare level' level < 0 ->
        x := { !x with value=Unrealised level' };
      | TADT (adt, adtlevel, _) when Level.compare adtlevel level' > 0->
        raise (Level_difference (adt, adtlevel, level'))
      | TUnit | TEmpty | TBool | TInt | TVar _
      | TUVar ({contents={value=Unrealised _;_}}) -> ()
      | TUVar ({contents={value=Realised tp;_}}) ->
        inner  tp
      | TADT (_, _, tps) ->
         List.iter inner tps
      | TArrow (targ, tres) ->
        inner targ;
        inner tres
      | TPair (tp1, tp2) ->
        inner tp1;
        inner tp2
    in inner tp

