open Core.Imast
open Core

(** Internal representation of types *)
module UVar = Tvar.Make()

type t =
  | TIUnit
  | TIEmpty
  | TIBool
  | TIInt
  | TIVar    of Imast.IMAstVar.t
  | TIADT    of Imast.IMAstVar.t * int * t list
  | TIUVar   of uvar
  | TIArrow  of t list * t
  | TIProd   of t list

and uvar_struct = {
  id: UVar.t;
  value: t option;
  is_gvar: bool;
  level: int
}
and uvar = uvar_struct ref
and view =
  | TUnit
  | TEmpty
  | TBool
  | TInt
  | TVar    of Imast.IMAstVar.t
  | TADT    of Imast.IMAstVar.t * int * t list
  | TGVar   of uvar * view option
  | TUVar   of uvar
  | TArrow  of t list * t
  | TProd   of t list

let t_unit  = TIUnit
let t_empty = TIEmpty
let t_bool  = TIBool
let t_int   = TIInt
let t_var x = TIVar x
let t_arrow  tps tp2 = TIArrow(tps, tp2)
let t_adt name level tps   = TIADT(name, level, tps)
let t_pair tp1 tp2 = TIProd([tp1; tp2])
let t_prod tps     = TIProd(tps)

let makeUvar value id gvar level =
  { value; id; is_gvar=gvar; level }
let is_gvar {contents={is_gvar;_}} = is_gvar
let id_of_uvar {contents={id;_}} = id
let lvl_of_uvar {contents={level;_}} = level

let fresh_uvar level = TIUVar (ref (makeUvar None (UVar.fresh ()) false level))
let fresh_gvar level = TIUVar (ref (makeUvar None (UVar.fresh ()) true level))

let rec view tp =
  let rec prune_uvar = function
    | TIUVar ({contents={ value=Some tp;_}} as x) ->
      let shortened = prune_uvar tp in
      x := { !x with value=Some shortened };
      shortened
    | tp -> tp
  in
  let view_uvar x =
    match !x with
    | {value=None; _} -> None
    | {value=Some tp; _ } ->
      let tp = prune_uvar tp in
      x := { !x with value=Some tp };
      Some (view tp)
  in
  match tp with
  | TIUVar x when is_gvar x ->
      TGVar (x, view_uvar x)
  | TIUVar ({contents={value=Some _;_}} as x) ->
      Option.get (view_uvar x)
  | TIUVar ({contents={value=None;_}} as x) ->
      TUVar x
  | TIVar x -> TVar x
  | TIADT (x, lvl, tps) -> TADT (x, lvl, tps)
  | TIUnit -> TUnit
  | TIEmpty -> TEmpty
  | TIBool -> TBool
  | TIInt -> TInt
  | TIArrow(tps, tp2) -> TArrow(tps, tp2)
  | TIProd tps -> TProd tps


exception Cannot_compare of t * t


let rec iter f : t -> unit =
  let default t = match t with
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _ | TIUVar ({contents={value=None;_}}) -> ()
    | TIUVar ({contents={value=Some tp;_}}) ->
      iter f tp
    | TIADT (_, _, tps) ->
       List.iter (iter f) tps
    | TIArrow (tps, tp) ->
      List.iter (iter f) tps;
      iter f tp
    | TIProd tps ->
      List.iter (iter f) tps
  in
  f default


let rec set_uvar x tp =
  lower_uvar_level x tp;
  match !x with
  | {value=None; _} -> x := {!x with value=Some tp }
  | {value=Some tp_current; is_gvar;_} when is_gvar ->
      let res = reconstruct tp tp_current in
      x := { !x with value=Some res }
  | { value=Some _;_ } ->
     assert false

and lower_uvar_level ({contents={level=level';_}} as x : uvar) tp =
  let rec helper default = function
    | TIUVar ({contents={ level; value=None;_}} as x) when level' < level ->
      x := { !x with level=level' };
    | TIUVar ({contents={ level; value=Some tp;_}} as x) when level' < level ->
      x:= { !x with level=level' };
      helper default tp;
    | TIADT (_, level, _) when level > level' ->
      raise (Cannot_compare (tp, (TIUVar x)))
    | tp -> default tp
  in iter helper tp

and reconstruct (new_tp : t) (current_tp : t) =
  let rec reconstruct_arrows (tpsa, resa) (tpsb, resb) =
    match tpsa, tpsb with
    | tpa :: tpsa, tpb :: tpsb ->
        (* because arguments in arrows are contravariant these are reversed *)
        let tp = reconstruct tpb tpa in
        let rest, res = reconstruct_arrows (tpsa, resa) (tpsb, resb) in
        tp :: rest, res
    | [], _ :: _ ->
        [], reconstruct resa (TIArrow (tpsb, resb))
    | _ :: _, [] ->
        [], reconstruct (TIArrow (tpsa, resa)) resb
    | [], [] ->
        [], reconstruct resa resb
  in
  let uvar_map x tp fn =
    match !x with
      | {value=None;_} ->
        x := { !x with value=Some tp };
        tp
      | {value=Some tp;_} ->
        let res = fn tp in
        x := { !x with value=Some res };
        res
  in
  match new_tp, current_tp with
  | TIUVar x, TIADT (_, adt_lvl, _)
  | TIADT (_, adt_lvl, _), TIUVar x when adt_lvl > lvl_of_uvar x ->
    raise (Cannot_compare (new_tp, current_tp))

  | TIUVar x, _ when is_gvar x ->
      uvar_map x current_tp (fun tp -> reconstruct tp current_tp)
  | TIUVar x, _ ->
      uvar_map x current_tp (fun _ -> raise (Cannot_compare (new_tp, current_tp)))
  | _, TIUVar x when is_gvar x ->
      uvar_map x new_tp (fun tp -> reconstruct new_tp tp)
  | _, TIUVar x ->
      uvar_map x new_tp (fun _ -> raise (Cannot_compare (new_tp, current_tp)))

  | TIUnit, TIUnit -> TIUnit

  (* Here is a good design question, does this rule make sense *)
  | _, TIUnit    -> TIUnit
  | TIUnit, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIEmpty, TIEmpty -> TIEmpty
  | TIEmpty, _     -> TIEmpty
  | _, TIEmpty -> raise (Cannot_compare (new_tp, current_tp))

  | TIVar _, _
  | _, TIVar _ ->
      raise (Cannot_compare (new_tp, current_tp))

  | TIADT (new_adt, new_lvl, new_tps),
    TIADT (cur_adt, cur_lvl, cur_tps) when IMAstVar.compare new_adt cur_adt = 0 ->
      assert (cur_lvl==new_lvl);
      (* pytanie: czy tutaj nie powinno być contrawariantne *)
      TIADT (new_adt, new_lvl, List.map2 reconstruct new_tps cur_tps)
  | TIADT _, _ ->
    raise (Cannot_compare (new_tp, current_tp))

  | TIBool, TIBool -> TIBool
  | TIBool, _ -> raise (Cannot_compare (new_tp, current_tp))
  | TIInt, TIInt -> TIInt
  | TIInt, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIArrow (tpsa, tp_resa),
    TIArrow (tpsb, tp_resb) ->
      let args, res = reconstruct_arrows (tpsa, tp_resa) (tpsb, tp_resb) in
      t_arrow args res
  | TIArrow _, _ -> raise (Cannot_compare (new_tp, current_tp))

  | TIProd(ts1), TIProd(ts2) when List.length ts1 = List.length ts2 ->
      TIProd (List.map2 reconstruct ts1 ts2)
  | TIProd _, _ -> raise (Cannot_compare (new_tp, current_tp))

let t_of_uvar { contents={value;_} } = value
let uvar_compare { contents={id=id1;_}} { contents={id=id2;_}} = UVar.compare id1 id2

(* TODO: implement this *)
let uvar_disallow_alias u alias = failwith "unimplemented"

module UVarSet = Set.Make(struct
  type t = uvar
  let compare = uvar_compare
end)

module UVarMap = Map.Make(struct
  type t = uvar
  let compare = uvar_compare
end)

let rec map f : t -> t =
  let default t = match t with
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _ | TIUVar ({contents={value=None;_}}) -> t
    | TIUVar ({contents={value=Some tp;_}} as x) ->
      set_uvar x (map f tp);
      TIUVar x
    | TIADT (name, lvl, tps) ->
      TIADT (name, lvl, List.map (map f) tps)
    | TIArrow (tps, tp) ->
      TIArrow (List.map (map f) tps, map f tp)
    | TIProd tps ->
      TIProd (List.map (map f) tps)
  in
  f default


let rec foldr f t init =
  let rec default init t = match t with
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _ | TIUVar ({contents={value=None;_}}) -> init
    | TIADT (_, _, tps) ->
      List.fold_right (foldr f) tps init
    | TIUVar ({contents={value=Some tp;_}}) ->
      f default (foldr f tp init) tp
    | TIProd tps ->
      List.fold_right (foldr f) tps init
    | TIArrow (tps, tp) ->
      f default (List.fold_right (foldr f) tps init) tp
  in
  f default (foldr f t init) t

let rec foldl f init t =
  let rec default init t = match t with
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _ | TIUVar ({contents={value=None;_}}) -> init
    | TIADT (_, _, tps) ->
      List.fold_left (foldl f) init tps
    | TIUVar ({contents={value=Some tp;_}}) ->
      foldl f (f default init tp) tp
    | TIProd tps ->
      List.fold_left (foldl f) init tps
    | TIArrow (tps, tp) ->
      List.fold_left (foldl f) (f default init tp) tps
  in
  foldl f (f default init t) t


type typ =
  | Mono of t
  | Schema of t * UVarSet.t

let typ_mono t = Mono t
let typ_schema set t = Schema (t, set)

let instantiate ?(mapping=UVarMap.empty) level = function
  | Mono tp -> tp
  | Schema (tp, uvars) ->
      let uvars_seq =
        UVarSet.to_seq uvars |>
        Seq.filter (fun x -> UVarMap.mem x mapping |> not) |>
        Seq.flat_map (fun x -> Seq.return (x, fresh_uvar level)) in
      let mapper = UVarMap.add_seq uvars_seq mapping in
      let instantiate default tp = match tp with
        | TIUVar x ->
            UVarMap.find_opt x mapper |> Option.value ~default:tp
        | tp -> default tp
      in map instantiate tp

let get_uvars t =
  let helper default (blacklist, acc) tp = match tp with
    | TIUVar x when UVarSet.mem x blacklist |> not ->
      blacklist, UVarSet.add x acc
    | tp -> default (blacklist, acc) tp
  in match t with
    | Mono t             -> foldl helper (UVarSet.empty, UVarSet.empty) t |> snd
    | Schema (tp, uvars) -> foldl helper (uvars, UVarSet.empty) tp |> snd

let generalize env_uvars tp =
  let tp_uvars  = get_uvars (typ_mono tp) in
  let diff = UVarSet.diff tp_uvars env_uvars in
  typ_schema diff tp

