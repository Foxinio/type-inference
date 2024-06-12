open Main
open Core.Imast

(* Join operation
 * (τ₁, τ₂) -> (τ₃) -> τ₄
 *    ⨆
 * (τ₁) -> (τ₂, τ₃) -> τ₄
 *    =>
 * (τ₁, τ₂, τ₃) -> τ₄
 *
 *)
let rec join (new_tp : t) (current_tp : t) =
  match new_tp, current_tp with
  | TIUVar x, _ ->
    join_with_uvar x (Either.Right current_tp)
  | _, TIUVar x ->
    join_with_uvar x (Either.Left new_tp)

  | TIUnit, TIUnit    -> TIUnit
  | TIUnit, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIEmpty, _     -> TIEmpty
  | _, TIEmpty -> raise (Cannot_compare (new_tp, current_tp))

  | TIVar x, TIVar y when x = y -> TIVar x
  | TIVar _, _
  | _, TIVar _ ->
      raise (Cannot_compare (new_tp, current_tp))

  | TIADT _, TIADT _ when equal new_tp current_tp ->
      new_tp
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
      let tp = meet tpb tpa in
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
      begin match join resa resb with
      | TIArrow (tps, tpres) -> tps, tpres
      | tpres -> [], tpres
      end

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

  | {value=Realised new_tp;_}, Right current_tp
  | {value=Realised current_tp;_}, Left new_tp ->
    join new_tp current_tp

(* Meet operation
 * (τ₁, τ₂) -> (τ₃) -> τ₄
 *    ⨅
 * (τ₁) -> (τ₂, τ₃) -> τ₄
 *    =>
 * (τ₁) -> (τ₂) -> (τ₃) -> τ₄
 *
 *)
and meet (new_tp : t) (current_tp : t) =
  match new_tp, current_tp with
  | TIUVar x, _ ->
    meet_with_uvar x (Either.Right current_tp)
  | _, TIUVar x ->
    meet_with_uvar x (Either.Left new_tp)

  | TIUnit, TIUnit    -> TIUnit
  | TIUnit, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIEmpty, TIEmpty  -> TIEmpty
  | TIEmpty, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIVar x, TIVar y when x = y -> TIVar x
  | TIVar _, _
  | _, TIVar _ ->
      raise (Cannot_compare (new_tp, current_tp))

  | TIADT (new_adt, new_lvl, new_tps),
    TIADT (cur_adt, cur_lvl, cur_tps)
      when equal new_tp current_tp ->
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
      let args, res = meet_arrows (tpsa, tp_resa) (tpsb, tp_resb) in
      t_arrow args res
  | TIArrow _, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIPair(tp1a, tp1b), TIPair(tp2a, tp2b) ->
      TIPair (meet tp1a tp2a, meet tp1b tp2b)
  | TIPair _, _ -> raise (Cannot_compare (new_tp, current_tp))

and meet_arrows (tpsa, resa) (tpsb, resb) =
  match tpsa, tpsb with
  | tpa :: tpsa, tpb :: tpsb ->
      let tp = join tpb tpa in
      let rest, res = meet_arrows (tpsa, resa) (tpsb, resb) in
      tp :: rest, res
  | [], _ :: _ ->
      [], meet resa (TIArrow (tpsb, resb))
  | _ :: _, [] ->
      [], meet (TIArrow (tpsa, resa)) resb
  | [], [] ->
      [], meet resa resb

and meet_with_uvar ?(loop=false) x tp =
  match !x, tp with
  | {value=Unrealised _;_}, Right tp
  | {value=Unrealised _;_}, Left tp ->
    x := { !x with value=Realised tp };
    tp
  | {value=Realised new_tp; is_gvar=true;_}, Right current_tp
  | {value=Realised current_tp; is_gvar=true;_}, Left new_tp ->
    let res = meet new_tp current_tp in
    x := { !x with value=Realised res };
    res
  | {value=Realised _; is_gvar=false;_}, Left (TIUVar y) when not loop ->
      meet_with_uvar y ~loop:true (Right (TIUVar x))
  | {value=Realised _; is_gvar=false;_}, Right (TIUVar y) when not loop ->
      meet_with_uvar y ~loop:true (Left (TIUVar x))

  | {value=Realised new_tp;_}, Right current_tp
  | {value=Realised current_tp;_}, Left new_tp ->
    meet new_tp current_tp

and equal t1 t2 = match t1, t2 with
  | TIUVar x, _ ->
    equal_with_uvar x (Either.Right t2)
  | _, TIUVar x ->
    equal_with_uvar x (Either.Left t1)

  | TIUnit, TIUnit -> true
  | TIUnit, _ -> false

  | TIEmpty, TIEmpty -> true
  | TIEmpty, _ -> false

  | TIVar x, TIVar y when x = y -> true
  | TIVar _, _ -> false

  | TIADT (new_adt, new_lvl, new_tps),
    TIADT (cur_adt, cur_lvl, cur_tps)
      when IMAstVar.compare new_adt cur_adt = 0
      && List.equal equal new_tps cur_tps ->
      assert (cur_lvl = new_lvl);
      true
  | TIADT _, _ -> false

  | TIBool, TIBool -> true
  | TIBool, _ -> false
  | TIInt, TIInt -> true
  | TIInt, _ -> false

  | TIArrow (tpsa, tp_resa),
    TIArrow (tpsb, tp_resb) when List.length tpsa = List.length tpsb ->
    equal tp_resa tp_resb && List.equal equal tpsa tpsb
  | TIArrow _, _ -> false

  | TIPair(tp1a, tp1b), TIPair(tp2a, tp2b) ->
      equal tp1a tp2a && equal tp1b tp2b
  | TIPair _, _ -> false

and equal_with_uvar ?(loop=false) x tp =
  match !x, tp with
  | {value=Unrealised _;_}, Right tp
  | {value=Unrealised _;_}, Left tp ->
    true
  | {value=Realised tp1;_}, Right tp2
  | {value=Realised tp2;_}, Left tp1 ->
    equal tp1 tp2


and subtype_impl subtype supertype =
  match subtype, supertype with
  | TIUVar x, _ ->
    subtype_with_uvar x (Either.Right supertype)
  | _, TIUVar x ->
    subtype_with_uvar x (Either.Left subtype)

  | TIUnit, _ | TIVar _, _ | TIADT _, _ | TIBool, _ | TIInt, _ ->
    equal subtype supertype

  | TIEmpty, _     -> true
  | _, TIEmpty -> false

  | TIArrow (tpsa, tp_resa),
    TIArrow (tpsb, tp_resb) ->
      subtype_arrows (tpsa, tp_resa) (tpsb, tp_resb)
  | TIArrow _, _ -> false

  | TIPair(tp1a, tp1b), TIPair(tp2a, tp2b) ->
      subtype_impl tp1a tp2a && subtype_impl tp1b tp2b
  | TIPair _, _ -> false

and subtype_arrows (tpsa, resa) (tpsb, resb) =
  match tpsa, tpsb with
  | tpa :: tpsa, tpb :: tpsb ->
      subtype_impl tpb tpa
      && subtype_arrows (tpsa, resa) (tpsb, resb)
  | [], _ :: _ ->
      subtype_impl resa (TIArrow (tpsb, resb))
  | _ :: _, [] ->
      false
  | [], [] ->
      subtype_impl resa resb

and subtype_with_uvar ?(loop=false) x tp =
  match !x, tp with
  | {value=Unrealised _;_}, Right tp
  | {value=Unrealised _;_}, Left tp ->
    x := { !x with value=Realised tp };
    true
  | {value=Realised subtype; _}, Right supertype
  | {value=Realised supertype; _}, Left subtype ->
    subtype_impl subtype supertype


let supertype ~supertype ~subtype =
  subtype_impl supertype subtype

let subtype ~subtype ~supertype =
  subtype_impl subtype supertype
