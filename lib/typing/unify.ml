open Core.Imast
open Core

open Type

(* ========================================================================= *)
(* Unification *)

exception Cannot_unify

let unwrap node env var opt =
  let var_name env var =
      Env.lookup_var_name env var in
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


let rec equal tp1 tp2 =
  let rec inner = function
    | TUVar (x), TUVar (y)
    | TGVar (x, None), TGVar (y, None) when x == y -> ()

    | _, TUVar (x) -> unify_with_uvar x tp1
    | TUVar (x), _ -> unify_with_uvar x tp2

    | _, TGVar (x, None) -> unify_with_uvar x tp1
    | TGVar (x, None), _ -> unify_with_uvar x tp2

    | TGVar (_, Some tp1), tp2 -> inner (tp1, tp2)
    | tp1, TGVar (_, Some tp2) -> inner (tp1, tp2)

    | TADT (x, lvl1, tps1), TADT (y, lvl2, tps2) when IMAstVar.compare x y = 0 -> 
      assert(lvl1=lvl2);
      List.iter2 equal tps1 tps2
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
      List.iter2 equal ta1 ta2;
      equal tb1 tb2
    | TArrow _, _ -> raise Cannot_unify

    | TPair(tp1a, tp1b), TPair(tp2a, tp2b) ->
      equal tp1a tp2a;
      equal tp1b tp2b
    | TPair _, _ -> raise Cannot_unify
  in
  inner (Type.view tp1, Type.view tp2)

let rec unify_subtype supertype subtype =
  let rec inner = function
    (* this requires some attension *)
    | TGVar (x, Some(TArrow _)), TArrow _ ->
      unify_with_uvar x subtype
    (* | TArrow _, TGVar (x, Some(TArrow _)) -> *)
    (*   unify_with_uvar x supertype *)

    | TGVar (_, Some tp1), tp2 -> inner (tp1, tp2)
    | tp1, TGVar (_, Some tp2) -> inner (tp1, tp2)

    | TArrow(tps1, tp1), TArrow(tps2, tp2) ->
      unify_subarrow tps1 tp1 tps2 tp2
    | TArrow _, _ -> raise Cannot_unify

    | TPair(tp1a, tp1b), TPair(tp2a, tp2b) ->
      unify_subtype tp1a tp2a;
      unify_subtype tp1b tp2b
    | TPair _, _ -> raise Cannot_unify

    | TUVar _, _
    | _, TUVar _
    | TGVar _, _
    | _, TGVar _
    | TADT _, _
    | TVar _, _
    | TUnit, _
    | TEmpty, _
    | TBool, _
    | TInt, _ -> 
      equal supertype subtype
  in inner (Type.view supertype, Type.view subtype)


and unify_subarrow tps1 tp1 tps2 tp2 =
  (* this is impelemnted correctly 10/05/24 *)
  let rec inner = function
    | [tp1'], tp2' :: (_ :: _ as tps2) ->
      unify_subtype tp2' tp1';
      begin match Type.view tp1 with
      | TArrow (tps1, tp1) ->
        unify_subarrow tps1 tp1 tps2 tp2
      | TGVar (x, Some (TArrow (tps1, tp1))) ->
        unify_subarrow tps1 tp1 tps2 tp2
      | TUVar x | TGVar (x, None) ->
        unify_with_uvar x (Type.t_arrow tps2 tp2)
      | _ -> raise Cannot_unify
      end
    | tp1' :: tps1, tp2' :: tps2 ->
      unify_subtype tp2' tp1'; 
      inner (tps1, tps2)
    | [], [] ->
      unify_subtype tp1 tp2
    | _, []
    | [], _ ->
      raise Cannot_unify
  in
  inner (tps1,tps2)


let subtype ~supertype ~subtype =
  unify_subtype supertype subtype
