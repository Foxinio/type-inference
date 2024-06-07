open Main
open Core.Imast

exception Cannot_compare of t * t

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
      let res = join tp tp_current in
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
      | TIArrow (tps, tp) ->
        List.iter inner tps;
        inner  tp
      | TIPair (tp1, tp2) ->
        inner tp1;
        inner tp2
    in inner tp

(* Join operation
 * (τ₁, τ₂) -> (τ₃) -> τ₄
 *    ⊔
 * (τ₁) -> (τ₂, τ₃) -> τ₄
 *    =>
 * (τ₁) -> (τ₂) -> (τ₃) -> τ₄
 *
 *)
and join (new_tp : t) (current_tp : t) =
  match new_tp, current_tp with

  (* when we try to unify UVar and ADT with higher level
     we should get an error *)
  | TIUVar ({contents={value=Unrealised uvar_lvl;_}}), TIADT (_, adt_lvl, _)
  | TIADT (_, adt_lvl, _), TIUVar ({contents={value=Unrealised uvar_lvl;_}})
      when Level.compare adt_lvl uvar_lvl > 0 ->
    raise (Cannot_compare (new_tp, current_tp))

  | TIUVar x, _ ->
    join_with_uvar x (Either.Right current_tp)
  | _, TIUVar x ->
    join_with_uvar x (Either.Left new_tp)

  | TIUnit, TIUnit    -> TIUnit
  | TIUnit, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIEmpty, _     -> TIEmpty
  | _, TIEmpty -> raise (Cannot_compare (new_tp, current_tp))

  | TIVar _, _
  | _, TIVar _ ->
      raise (Cannot_compare (new_tp, current_tp))

  | TIADT (new_adt, new_lvl, new_tps),
    TIADT (cur_adt, cur_lvl, cur_tps)
      when IMAstVar.compare new_adt cur_adt = 0 ->
      assert (cur_lvl = new_lvl);
      assert (new_tp = current_tp);
      TIADT (new_adt, new_lvl, new_tps)
  | TIADT _, _ ->
    raise (Cannot_compare (new_tp, current_tp))

  | TIBool, TIBool -> TIBool
  | TIBool, _ -> raise (Cannot_compare (new_tp, current_tp))
  | TIInt, TIInt -> TIInt
  | TIInt, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIArrow (tpsa, tp_resa),
    TIArrow (tpsb, tp_resb) ->
      let args, res = join_arrows (tpsa, tp_resa) (tpsb, tp_resb) in
      t_arrow args res
  | TIArrow _, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIPair(tp1a, tp1b), TIPair(tp2a, tp2b) ->
      TIPair (join tp1a tp2a, join tp1b tp2b)
  | TIPair _, _ -> raise (Cannot_compare (new_tp, current_tp))

and join_arrows (tpsa, resa) (tpsb, resb) =
  match tpsa, tpsb with
  | tpa :: tpsa, tpb :: tpsb ->
      (* TODO: call meet here *)
      let tp = join tpb tpa in
      let rest, res = join_arrows (tpsa, resa) (tpsb, resb) in
      tp :: rest, res
  | [], _ :: _ ->
      begin match join resa (TIArrow (tpsb, resb)) with
      | TIArrow (tps, tpres) -> tps, tpres
      | tpres -> [], tpres
      end
  | _ :: _, [] ->
      begin match join (TIArrow (tpsa, resa)) resb with
      | TIArrow (tps, tpres) -> tps, tpres
      | tpres -> [], tpres
      end
  | [], [] ->
      [], join resa resb

and join_with_uvar ?(loop=false) x tp =
  match !x, tp with
    | {value=Unrealised _;_}, Right tp
    | {value=Unrealised _;_}, Left tp ->
      x := { !x with value=Realised tp };
      tp
    | {value=Realised new_tp; is_gvar=true;_}, Right current_tp
    | {value=Realised current_tp; is_gvar=true;_}, Left new_tp ->
      let res = join new_tp current_tp in
      x := { !x with value=Realised res };
      res
    | {value=Realised _; is_gvar=false;_}, Left (TIUVar y) when not loop ->
        join_with_uvar y ~loop:true (Right (TIUVar x))
    | {value=Realised _; is_gvar=false;_}, Right (TIUVar y) when not loop ->
        join_with_uvar y ~loop:true (Left (TIUVar x))
    | {value=Realised _; is_gvar=false;_}, _ ->
      failwith "tried join on non gvar"




