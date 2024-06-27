open Main
open Core
open Imast


(* TODO: Fix this mess *)

(* Join operation
 * (τ₁, τ₂) -> (τ₃) -> τ₄
 *    ⨆
 * (τ₁) -> (τ₂, τ₃) -> τ₄
 *    =>
 * (τ₁, τ₂, τ₃) -> τ₄
 *
 *)
let rec merge (new_tp : t) (current_tp : t) =
  match new_tp, current_tp with
  | TIUVar x, _ ->
    merge_with_uvar x (Either.Right current_tp)
  | _, TIUVar x ->
    merge_with_uvar x (Either.Left new_tp)

  | TIUnit, TIUnit    -> TIUnit
  | TIUnit, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIEmpty, _     -> TIEmpty
  | _, TIEmpty -> raise (Cannot_compare (new_tp, current_tp))

  | TIVar x, TIVar y when x = y -> TIVar x
  | TIVar _, _
  | _, TIVar _ ->
      raise (Cannot_compare (new_tp, current_tp))

  | TIADT _, TIADT _ when equal new_tp current_tp -> new_tp
  | TIADT _, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIBool, TIBool -> TIBool
  | TIBool, _ -> raise (Cannot_compare (new_tp, current_tp))
  | TIInt, TIInt -> TIInt
  | TIInt, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIArrow (effa, tpsa, tp_resa),
    TIArrow (effb, tpsb, tp_resb) ->
      let eff = Effect.join effa effb in
      let args, res = merge_arrows (tpsa, tp_resa) (tpsb, tp_resb) in
      t_arrow eff args res
  | TIArrow _, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIPair(tp1a, tp1b), TIPair(tp2a, tp2b) ->
      TIPair (merge tp1a tp2a, merge tp1b tp2b)
  | TIPair _, _ -> raise (Cannot_compare (new_tp, current_tp))

(* and merge_pure_arrows (tpsa, resa) (tpsb, resb) = *)
(*   match tpsa, tpsb with *)
(*   | tpa :: tpsa, tpb :: tpsb -> *)
(*       let tp = split tpb tpa in *)
(*       let rest, res = merge_pure_arrows (tpsa, resa) (tpsb, resb) in *)
(*       tp :: rest, res *)
(*   | [], _ :: _ -> *)
(*       begin match merge resa (TIPureArrow (tpsb, resb)) with *)
(*       | TIPureArrow (tps, tpres) -> tps, tpres *)
(*       | tpres -> [], tpres *)
(*       end *)
(*   | _ :: _, [] -> *)
(*       begin match merge (TIPureArrow (tpsa, resa)) resb with *)
(*       | TIPureArrow (tps, tpres) -> tps, tpres *)
(*       | tpres -> [], tpres *)
(*       end *)
(*   | [], [] -> *)
(*       begin match merge resa resb with *)
(*       | TIPureArrow (tps, tpres) -> tps, tpres *)
(*       | tpres -> [], tpres *)
(*       end *)

and merge_arrows (tpsa, resa) (tpsb, resb) =
  match tpsa, tpsb with
  | tpa :: tpsa, tpb :: tpsb ->
      let tp = split tpb tpa in
      let rest, res = merge_arrows (tpsa, resa) (tpsb, resb) in
      tp :: rest, res
  | [], _ :: _ ->
      begin match merge resa (TIArrow (Impure, tpsb, resb)) with
      | TIArrow (_, tps, tpres) -> tps, tpres
      | tpres -> [], tpres
      end
  | _ :: _, [] ->
      begin match merge (TIArrow (Impure, tpsa, resa)) resb with
      | TIArrow (_, tps, tpres) -> tps, tpres
      | tpres -> [], tpres
      end
  | [], [] ->
      begin match merge resa resb with
      | TIArrow (_, tps, tpres) -> tps, tpres
      | tpres -> [], tpres
      end

and merge_with_uvar ?(loop=false) x tp =
  match !x, tp with
  | {value=Unrealised _;_}, Right tp
  | {value=Unrealised _;_}, Left tp ->
    x := { !x with value=Realised tp };
    tp
  | {value=Realised new_tp; is_gvar=true;_}, Right current_tp
  | {value=Realised current_tp; is_gvar=true;_}, Left new_tp ->
    let res = merge new_tp current_tp in
    x := { !x with value=Realised res };
    res
  | {value=Realised _; is_gvar=false;_}, Left (TIUVar y) when not loop ->
      merge_with_uvar y ~loop:true (Right (TIUVar x))
  | {value=Realised _; is_gvar=false;_}, Right (TIUVar y) when not loop ->
      merge_with_uvar y ~loop:true (Left (TIUVar x))

  | {value=Realised new_tp;_}, Right current_tp
  | {value=Realised current_tp;_}, Left new_tp ->
    merge new_tp current_tp

(* Meet operation
 * (τ₁, τ₂) -> (τ₃) -> τ₄
 *    ⨅
 * (τ₁) -> (τ₂, τ₃) -> τ₄
 *    =>
 * (τ₁) -> (τ₂) -> (τ₃) -> τ₄
 *
 *)
and split (new_tp : t) (current_tp : t) =
  match new_tp, current_tp with
  | TIUVar x, _ ->
    split_with_uvar x (Either.Right current_tp)
  | _, TIUVar x ->
    split_with_uvar x (Either.Left new_tp)

  | TIUnit, TIUnit    -> TIUnit
  | TIUnit, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIEmpty, TIEmpty  -> TIEmpty
  | TIEmpty, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIVar x, TIVar y when x = y -> TIVar x
  | TIVar _, _
  | _, TIVar _ ->
      raise (Cannot_compare (new_tp, current_tp))

  | TIADT _, TIADT _ when equal new_tp current_tp -> new_tp
  | TIADT _, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIBool, TIBool -> TIBool
  | TIBool, _ -> raise (Cannot_compare (new_tp, current_tp))
  | TIInt, TIInt -> TIInt
  | TIInt, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIArrow (effa, tpsa, tp_resa),
    TIArrow (effb, tpsb, tp_resb) ->
      let eff = Effect.join effa effb in
      let args, res = split_arrows (tpsa, tp_resa) (tpsb, tp_resb) in
      t_arrow eff args res
  | TIArrow _, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIPair(tp1a, tp1b), TIPair(tp2a, tp2b) ->
      TIPair (split tp1a tp2a, split tp1b tp2b)
  | TIPair _, _ -> raise (Cannot_compare (new_tp, current_tp))

and split_arrows (tpsa, resa) (tpsb, resb) =
  match tpsa, tpsb with
  | tpa :: tpsa, tpb :: tpsb ->
      let tp = merge tpb tpa in
      let rest, res = split_arrows (tpsa, resa) (tpsb, resb) in
      tp :: rest, res
  | [], _ :: _ ->
      [], split resa (TIArrow (Impure, tpsb, resb))
  | _ :: _, [] ->
      [], split (TIArrow (Impure, tpsa, resa)) resb
  | [], [] ->
      [], split resa resb

(* and split_pure_arrows (tpsa, resa) (tpsb, resb) = *)
(*   match tpsa, tpsb with *)
(*   | tpa :: tpsa, tpb :: tpsb -> *)
(*       let tp = merge tpb tpa in *)
(*       let rest, res = split_pure_arrows (tpsa, resa) (tpsb, resb) in *)
(*       tp :: rest, res *)
(*   | [], _ :: _ -> *)
(*       [], split resa (TIPureArrow (tpsb, resb)) *)
(*   | _ :: _, [] -> *)
(*       [], split (TIPureArrow (tpsa, resa)) resb *)
(*   | [], [] -> *)
(*       [], split resa resb *)

and split_with_uvar ?(loop=false) x tp =
  match !x, tp with
  | {value=Unrealised _;_}, Right tp
  | {value=Unrealised _;_}, Left tp ->
    x := { !x with value=Realised tp };
    tp
  | {value=Realised new_tp; is_gvar=true;_}, Right current_tp
  | {value=Realised current_tp; is_gvar=true;_}, Left new_tp ->
    let res = split new_tp current_tp in
    x := { !x with value=Realised res };
    res
  | {value=Realised _; is_gvar=false;_}, Left (TIUVar y) when not loop ->
      split_with_uvar y ~loop:true (Right (TIUVar x))
  | {value=Realised _; is_gvar=false;_}, Right (TIUVar y) when not loop ->
      split_with_uvar y ~loop:true (Left (TIUVar x))

  | {value=Realised new_tp;_}, Right current_tp
  | {value=Realised current_tp;_}, Left new_tp ->
    split new_tp current_tp

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

  | TIArrow (effb, tpsa, tp_resa),
    TIArrow (effa, tpsb, tp_resb) when List.length tpsa = List.length tpsb ->
    equal tp_resa tp_resb
    && List.equal equal tpsa tpsb
    && effa = effb
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

  | TIArrow (effa, tpsa, tp_resa),
    TIArrow (effb, tpsb, tp_resb) ->
      subtype_arrows (Effect.join effa effb) (tpsa, tp_resa) (tpsb, tp_resb)
  | TIArrow _, _ -> false

  (* | TIPureArrow (tpsa, tp_resa), *)
  (*   TIPureArrow (tpsb, tp_resb) -> *)
  (*     subtype_pure_arrows (tpsa, tp_resa) (tpsb, tp_resb) *)
  (* | TIPureArrow _, _ -> false *)

  | TIPair(tp1a, tp1b), TIPair(tp2a, tp2b) ->
      subtype_impl tp1a tp2a && subtype_impl tp1b tp2b
  | TIPair _, _ -> false

and subtype_arrows eff (tpsa, resa) (tpsb, resb) =
  match tpsa, tpsb with
  | tpa :: tpsa, tpb :: tpsb ->
      subtype_impl tpb tpa
      && subtype_arrows eff (tpsa, resa) (tpsb, resb)
  | [], _ :: _ ->
      subtype_impl resa (TIArrow (eff, tpsb, resb))
  | _ :: _, [] ->
      false
  | [], [] ->
      subtype_impl resa resb

(* and subtype_pure_arrows (tpsa, resa) (tpsb, resb) = *)
(*   match tpsa, tpsb with *)
(*   | tpa :: tpsa, tpb :: tpsb -> *)
(*       subtype_impl tpb tpa *)
(*       && subtype_pure_arrows (tpsa, resa) (tpsb, resb) *)
(*   | [], _ :: _ -> *)
(*       subtype_impl resa (TIPureArrow (tpsb, resb)) *)
(*   | _ :: _, [] -> *)
(*       subtype_impl (TIPureArrow (tpsa, resa)) resb *)
(*   | [], [] -> *)
(*       subtype_impl resa resb *)

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
