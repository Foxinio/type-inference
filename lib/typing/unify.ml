open Core.Imast
open Core

open Type

(* ========================================================================= *)
(* Unification *)

exception Cannot_unify

let unwrap node env var opt =
  let var_name env var =
      Env.lookup_var_name env var |>
        Option.value ~default:"<unknown>" in
  match opt with
  | Some t -> t
  | None ->
    let name = var_name env var in
    Utils.report_error node "Undefined variable: %s" name

let contains_uvar x tp =
  let helper default init t = match Type.view t with
    | TUVar y -> Type.uvar_compare x y = 0
    | _ -> default init t
  in Type.foldl helper false tp


let unify_with_uvar x tp =
  if contains_uvar x tp then raise Cannot_unify
  else try
    Type.set_uvar x tp
  with Type.Cannot_compare _ ->
    raise Cannot_unify


let rec unify tp1 tp2 =
  let rec unify_int tpv1 tpv2 =
    match tpv1, tpv2 with
    | TUVar (x), TUVar (y)
    | TGVar (x, None), TGVar (y, None) when x == y -> ()

    | _, TUVar (x) -> unify_with_uvar x tp1
    | TUVar (x), _ -> unify_with_uvar x tp2

    | _, TGVar (x, None) -> unify_with_uvar x tp1
    | TGVar (x, None), _ -> unify_with_uvar x tp2

    | TGVar (x, Some(TArrow _)), TArrow _ ->
        unify_with_uvar x tp2
    | TArrow _, TGVar (x, Some(TArrow _)) ->
        unify_with_uvar x tp1

    | TGVar (_, Some tp1), tp2 -> unify_int tp1 tp2
    | tp1, TGVar (_, Some tp2) -> unify_int tp1 tp2

    | TADT (x, lvl1, tps1), TADT (y, lvl2, tps2) when IMAstVar.compare x y = 0 -> 
      assert(lvl1=lvl2);
      List.iter2 unify tps1 tps2
    | TADT _, _-> raise Cannot_unify

    | TVar x, TVar y when Type.TVar.compare x y = 0 -> ()
    | TVar _, _ -> raise Cannot_unify

    | TUnit, TUnit -> ()
    | TUnit, _ -> raise Cannot_unify

    | TEmpty, TEmpty -> ()
    | TEmpty, _ -> raise Cannot_unify

    | TBool, TBool -> ()
    | TBool, _ -> raise Cannot_unify

    | TInt, TInt -> ()
    | TInt, _ -> raise Cannot_unify

    | TArrow(ta1, tb1), TArrow(ta2, tb2) ->
      List.iter2 unify ta1 ta2;
      unify tb1 tb2
    | TArrow _, _ -> raise Cannot_unify

    | TProd(ts1), TProd(ts2) ->
      List.iter2 unify ts1 ts2
    | TProd _, _ -> raise Cannot_unify
  in
  unify_int (Type.view tp1) (Type.view tp2)

