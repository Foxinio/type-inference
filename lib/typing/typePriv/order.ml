open Main
open Core.Imast

(*

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
  | TUVar x, _ ->
    merge_with_uvar x (Either.Right current_tp)
  | _, TUVar x ->
    merge_with_uvar x (Either.Left new_tp)

  | TUnit, TUnit    -> TUnit
  | TUnit, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TEmpty, _     -> TEmpty
  | _, TEmpty -> raise (Cannot_compare (new_tp, current_tp))

  | TVar x, TVar y when x = y -> TVar x
  | TVar _, _
  | _, TVar _ ->
      raise (Cannot_compare (new_tp, current_tp))

  | TADT _, TADT _ when equal new_tp current_tp -> new_tp
  | TADT _, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TBool, TBool -> TBool
  | TBool, _ -> raise (Cannot_compare (new_tp, current_tp))
  | TInt, TInt -> TInt
  | TInt, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TArrow (effa, tpsa, tp_resa),
    TArrow (effb, tpsb, tp_resb) ->
      let eff = Effect.join effa effb in
      let args, res = merge_arrows (tpsa, tp_resa) (tpsb, tp_resb) in
      t_arrow eff args res
  | TArrow _, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TPair(tp1a, tp1b), TPair(tp2a, tp2b) ->
      TPair (merge tp1a tp2a, merge tp1b tp2b)
  | TPair _, _ -> raise (Cannot_compare (new_tp, current_tp))

(* and merge_pure_arrows (tpsa, resa) (tpsb, resb) = *)
(*   match tpsa, tpsb with *)
(*   | tpa :: tpsa, tpb :: tpsb -> *)
(*       let tp = split tpb tpa in *)
(*       let rest, res = merge_pure_arrows (tpsa, resa) (tpsb, resb) in *)
(*       tp :: rest, res *)
(*   | [], _ :: _ -> *)
(*       begin match merge resa (TPureArrow (tpsb, resb)) with *)
(*       | TPureArrow (tps, tpres) -> tps, tpres *)
(*       | tpres -> [], tpres *)
(*       end *)
(*   | _ :: _, [] -> *)
(*       begin match merge (TPureArrow (tpsa, resa)) resb with *)
(*       | TPureArrow (tps, tpres) -> tps, tpres *)
(*       | tpres -> [], tpres *)
(*       end *)
(*   | [], [] -> *)
(*       begin match merge resa resb with *)
(*       | TPureArrow (tps, tpres) -> tps, tpres *)
(*       | tpres -> [], tpres *)
(*       end *)

and merge_arrows (tpsa, resa) (tpsb, resb) =
  match tpsa, tpsb with
  | tpa :: tpsa, tpb :: tpsb ->
      let tp = split tpb tpa in
      let rest, res = merge_arrows (tpsa, resa) (tpsb, resb) in
      tp :: rest, res
  | [], _ :: _ ->
      begin match merge resa (TArrow (EffImpure, tpsb, resb)) with
      | TArrow (_, tps, tpres) -> tps, tpres
      | tpres -> [], tpres
      end
  | _ :: _, [] ->
      begin match merge (TArrow (EffImpure, tpsa, resa)) resb with
      | TArrow (_, tps, tpres) -> tps, tpres
      | tpres -> [], tpres
      end
  | [], [] ->
      begin match merge resa resb with
      | TArrow (_, tps, tpres) -> tps, tpres
      | tpres -> [], tpres
      end

and merge_with_uvar ?(loop=false) x tp =
  match !x, tp with
  | {value=Unrealised _;_}, Right tp
  | {value=Unrealised _;_}, Left tp ->
    x := { !x with value=Realised tp };
    tp
  | {value=Realised _; _}, Left (TUVar y) when not loop ->
      merge_with_uvar y ~loop:true (Right (TUVar x))
  | {value=Realised _; _}, Right (TUVar y) when not loop ->
      merge_with_uvar y ~loop:true (Left (TUVar x))

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
  | TUVar x, _ ->
    split_with_uvar x (Either.Right current_tp)
  | _, TUVar x ->
    split_with_uvar x (Either.Left new_tp)

  | TUnit, TUnit    -> TUnit
  | TUnit, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TEmpty, TEmpty  -> TEmpty
  | TEmpty, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TVar x, TVar y when x = y -> TVar x
  | TVar _, _
  | _, TVar _ ->
      raise (Cannot_compare (new_tp, current_tp))

  | TADT _, TADT _ when equal new_tp current_tp -> new_tp
  | TADT _, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TBool, TBool -> TBool
  | TBool, _ -> raise (Cannot_compare (new_tp, current_tp))
  | TInt, TInt -> TInt
  | TInt, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TArrow (effa, tpsa, tp_resa),
    TArrow (effb, tpsb, tp_resb) ->
      let eff = Effect.join effa effb in
      let args, res = split_arrows (tpsa, tp_resa) (tpsb, tp_resb) in
      t_arrow eff args res
  | TArrow _, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TPair(tp1a, tp1b), TPair(tp2a, tp2b) ->
      TPair (split tp1a tp2a, split tp1b tp2b)
  | TPair _, _ -> raise (Cannot_compare (new_tp, current_tp))

and split_arrows (tpsa, resa) (tpsb, resb) =
  match tpsa, tpsb with
  | tpa :: tpsa, tpb :: tpsb ->
      let tp = merge tpb tpa in
      let rest, res = split_arrows (tpsa, resa) (tpsb, resb) in
      tp :: rest, res
  | [], _ :: _ ->
      [], split resa (TArrow (EffImpure, tpsb, resb))
  | _ :: _, [] ->
      [], split (TArrow (EffImpure, tpsa, resa)) resb
  | [], [] ->
      [], split resa resb

(* and split_pure_arrows (tpsa, resa) (tpsb, resb) = *)
(*   match tpsa, tpsb with *)
(*   | tpa :: tpsa, tpb :: tpsb -> *)
(*       let tp = merge tpb tpa in *)
(*       let rest, res = split_pure_arrows (tpsa, resa) (tpsb, resb) in *)
(*       tp :: rest, res *)
(*   | [], _ :: _ -> *)
(*       [], split resa (TPureArrow (tpsb, resb)) *)
(*   | _ :: _, [] -> *)
(*       [], split (TPureArrow (tpsa, resa)) resb *)
(*   | [], [] -> *)
(*       [], split resa resb *)

and split_with_uvar ?(loop=false) x tp =
  match !x, tp with
  | {value=Unrealised _;_}, Right tp
  | {value=Unrealised _;_}, Left tp ->
    x := { !x with value=Realised tp };
    tp
  | {value=Realised _; _}, Left (TUVar y) when not loop ->
      split_with_uvar y ~loop:true (Right (TUVar x))
  | {value=Realised _; _}, Right (TUVar y) when not loop ->
      split_with_uvar y ~loop:true (Left (TUVar x))

  | {value=Realised new_tp;_}, Right current_tp
  | {value=Realised current_tp;_}, Left new_tp ->
    split new_tp current_tp
*)

let rec equal t1 t2 = match t1, t2 with
  | TUVar x, _ ->
    equal_with_uvar x t2
  | _, TUVar x ->
    equal_with_uvar x t1

  | TUnit, TUnit -> true
  | TUnit, _ -> false

  | TEmpty, TEmpty -> true
  | TEmpty, _ -> false

  | TVar x, TVar y when x = y -> true
  | TVar _, _ -> false

  | TADT (new_adt, new_lvl, new_tps),
    TADT (cur_adt, cur_lvl, cur_tps)
      when IMAstVar.compare new_adt cur_adt = 0
      && List.equal equal new_tps cur_tps ->
      assert (cur_lvl = new_lvl);
      true
  | TADT _, _ -> false

  | TBool, TBool -> true
  | TBool, _ -> false
  | TInt, TInt -> true
  | TInt, _ -> false

  | TArrow (effb, targa, tresa),
    TArrow (effa, targb, tresb) ->
    let open Effect in
    equal tresa tresb
    && equal targa targb
    && equal_mod_known !effa !effb
  | TArrow _, _ -> false

  | TPair(tp1a, tp1b), TPair(tp2a, tp2b) ->
      equal tp1a tp2a && equal tp1b tp2b
  | TPair _, _ -> false

and equal_with_uvar x tp =
  match !x, tp with
  | {value=Unrealised _;_}, _ ->
    true
  | {value=Realised tp2;_}, tp1 ->
    equal tp1 tp2


(*
and subtype_impl subtype supertype =
  match subtype, supertype with
  | TUVar x, _ ->
    subtype_with_uvar x (Either.Right supertype)
  | _, TUVar x ->
    subtype_with_uvar x (Either.Left subtype)

  | TUnit, _ | TVar _, _ | TADT _, _ | TBool, _ | TInt, _ ->
    equal subtype supertype

  | TEmpty, _     -> true
  | _, TEmpty -> false

  | TArrow (effa, tpsa, tp_resa),
    TArrow (effb, tpsb, tp_resb) ->
      subtype_arrows (Effect.join effa effb) (tpsa, tp_resa) (tpsb, tp_resb)
  | TArrow _, _ -> false

  (* | TPureArrow (tpsa, tp_resa), *)
  (*   TPureArrow (tpsb, tp_resb) -> *)
  (*     subtype_pure_arrows (tpsa, tp_resa) (tpsb, tp_resb) *)
  (* | TPureArrow _, _ -> false *)

  | TPair(tp1a, tp1b), TPair(tp2a, tp2b) ->
      subtype_impl tp1a tp2a && subtype_impl tp1b tp2b
  | TPair _, _ -> false

and subtype_arrows eff (tpsa, resa) (tpsb, resb) =
  match tpsa, tpsb with
  | tpa :: tpsa, tpb :: tpsb ->
      subtype_impl tpb tpa
      && subtype_arrows eff (tpsa, resa) (tpsb, resb)
  | [], _ :: _ ->
      subtype_impl resa (TArrow (eff, tpsb, resb))
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
(*       subtype_impl resa (TPureArrow (tpsb, resb)) *)
(*   | _ :: _, [] -> *)
(*       subtype_impl (TPureArrow (tpsa, resa)) resb *)
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

*)

