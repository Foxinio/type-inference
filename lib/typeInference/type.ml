open Core.Imast
open Core

(** Internal representation of types *)
module UVar = Tvar.Make()

type t =
  | TIUnit
  | TIEmpty
  | TIBool
  | TIInt
  | TIVar    of Imast.IMAstVar.t * bool
  | TIADT    of Imast.IMAstVar.t * t list
  | TIUVar   of uvar
  | TIArrow  of t list * t
  | TIProd   of t list

and uvar_struct = { id: UVar.t; value: t option; is_gvar: bool }
and uvar = uvar_struct ref
and view =
  | TUnit
  | TEmpty
  | TBool
  | TInt
  | TVar    of Imast.IMAstVar.t
  | TADT    of Imast.IMAstVar.t * t list
  | TGVar   of uvar * view option
  | TUVar   of uvar
  | TArrow  of t list * t
  | TProd   of t list

let fresh_uvar () = TIUVar (ref { id=UVar.fresh (); value=None; is_gvar=false})
let fresh_gvar () = TIUVar (ref { id=UVar.fresh (); value=None; is_gvar=true })

let t_unit  = TIUnit
let t_empty = TIEmpty
let t_bool  = TIBool
let t_int   = TIInt
let t_arrow  tps tp2 = TIArrow(tps, tp2)
let t_adt name tps = TIADT(name, tps)
let t_pair   tp1 tp2 = TIProd([tp1; tp2])
let t_prod   tps = TIProd(tps)

let makeUvar value id gvar =
  { value; id; is_gvar=gvar }
let is_gvar {contents={is_gvar;_}} = is_gvar
let id_of_uvar {contents={id;_}} = id


let rec t_of_view = function
  | TUVar x -> TIUVar x
  | TGVar (x, _) -> TIUVar x
  | TVar x -> TIVar (x, false)
  | TADT(x, tps) -> TIADT(x, tps)
  | TUnit -> TIUnit
  | TEmpty -> TIEmpty
  | TBool -> TIBool
  | TInt -> TIInt
  | TArrow(tps, tp2) -> TIArrow(tps, tp2)
  | TProd tps -> TIProd tps

let rec view tp =
  let view_uvar x =
    match !x with
    | {value=None; _} -> None
    | {value=Some tp; id; is_gvar} ->
      let tp = view tp in
      x := { !x with value=Some (t_of_view tp) };
      Some tp
  in
  match tp with
  | TIUVar x when is_gvar x ->
      TGVar (x, view_uvar x)
  | TIUVar ({contents={value=Some _;_}} as x) ->
      Option.get (view_uvar x)
  | TIUVar ({contents={value=None;_}} as x) ->
      TUVar x
  | TIVar (x, _) -> TVar x
  | TIADT (x, tps) -> TADT (x, tps)
  | TIUnit -> TUnit
  | TIEmpty -> TEmpty
  | TIBool -> TBool
  | TIInt -> TInt
  | TIArrow(tps, tp2) -> TArrow(tps, tp2)
  | TIProd tps -> TProd tps


exception Cannot_compare of t * t

let rec set_uvar x tp =
  match !x with
  | {value=None; _} -> x := {!x with value=Some tp }
  | {value=Some tp_current; is_gvar;_} when is_gvar ->
      let res = reconstruct tp tp_current in
      x := { !x with value=Some res }
  | {value=Some _; _} ->
     assert false

and reconstruct (new_tp : t) (currrnet_tp : t) =
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
  match new_tp, currrnet_tp with
  | TIUVar x, _ when is_gvar x ->
      uvar_map x currrnet_tp (fun tp -> reconstruct tp currrnet_tp)
  | TIUVar x, _ ->
      uvar_map x currrnet_tp (fun _ -> raise (Cannot_compare (new_tp, currrnet_tp)))
  | _, TIUVar x when is_gvar x ->
      uvar_map x new_tp (fun tp -> reconstruct new_tp tp)
  | _, TIUVar x ->
      uvar_map x new_tp (fun _ -> raise (Cannot_compare (new_tp, currrnet_tp)))

  | TIUnit, TIUnit -> TIUnit

  (* Here is a good design question, does this rule make sense *)
  | _, TIUnit    -> TIUnit

  | TIEmpty, TIEmpty -> TIEmpty
  | TIEmpty, _     -> TIEmpty

  | TIBool, TIBool -> TIBool
  | TIInt, TIInt -> TIInt

  | TIArrow (tpsa, tp_resa),
    TIArrow (tpsb, tp_resb) ->
      let args, res = reconstruct_arrows (tpsa, tp_resa) (tpsb, tp_resb) in
      t_arrow args res

  | TIProd(ts1), TIProd(ts2) when List.length ts1 = List.length ts2 ->
    TIProd (List.map2 reconstruct ts1 ts2)
  | _, _ -> raise (Cannot_compare (new_tp, currrnet_tp))


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
  let default (t : view) : t = match t with
    | TUnit | TEmpty | TBool | TInt | TVar _ | TUVar _ | TGVar (_, None) -> t_of_view t
    | TADT (name, tps) ->
      TIADT (name, List.map (map f) tps)
    | TGVar (uvar, Some tp) ->
      set_uvar uvar (map f (t_of_view tp));
      TIUVar uvar
    | TArrow (tps, tp) ->
      TIArrow (List.map (map f) tps, map f tp)
    | TProd tps ->
      TIProd (List.map (map f) tps)
  in
  f default

let rec iter f : t -> unit =
  let default (t : view) : unit = match t with
    | TUnit | TEmpty | TBool | TInt | TVar _ | TUVar _ | TGVar (_, None) -> ()
    | TADT (name, tps) ->
       List.iter (iter f) tps
    | TGVar (_, Some tp) ->
      iter f (t_of_view tp)
    | TArrow (tps, tp) ->
      List.iter (iter f) tps;
      iter f tp
    | TProd tps ->
      List.iter (iter f) tps
  in
  f default

let rec foldr f t init =
  let rec default init t = match t with
    | TUnit | TEmpty | TBool | TInt | TVar _ | TUVar _ | TGVar (_, None) -> init
    | TADT (name, tps) ->
      List.fold_right (foldr f) tps init
    | TGVar (_, Some tp) ->
      f default (foldr f (t_of_view tp) init) (t_of_view tp)
    | TProd tps ->
      List.fold_right (foldr f) tps init
    | TArrow (tps, tp) ->
      f default (List.fold_right (foldr f) tps init) tp
  in
  f default (foldr f t init) t

let rec foldl f init t =
  let rec default init t = match t with
    | TUnit | TEmpty | TBool | TInt | TVar _ | TUVar _ | TGVar (_, None) -> init
    | TADT (name, tps) ->
      List.fold_left (foldl f) init tps
    | TGVar (_, Some tp) ->
      foldl f (f default init (t_of_view tp)) (t_of_view tp)
    | TProd tps ->
      List.fold_left (foldl f) init tps
    | TArrow (tps, tp) ->
      List.fold_left (foldl f) (f default init tp) tps
  in
  foldl f (f default init t) t


type typ =
  | Mono of t
  | Schema of t * UVarSet.t

let typ_mono t = Mono t
let typ_schema set t = Schema (t, set)

let instantiate ?(mapping=UVarMap.empty) = function
  | Mono tp -> tp
  | Schema (tp, uvars) ->
      let uvars_seq =
        UVarSet.to_seq uvars |>
        Seq.filter (fun x -> UVarMap.mem x mapping |> not) |>
        Seq.flat_map (fun x -> Seq.return (x, fresh_uvar ())) in
      let mapper = UVarMap.add_seq uvars_seq mapping in
      let rec instantiate default tp = match tp with
        | TIUVar x ->
            UVarMap.find_opt x mapper |> Option.value ~default:tp
        | tp -> view tp |> default
      in map instantiate tp

let get_uvars t =
  let helper default (blacklist, acc) tp = match view tp with
    | TUVar x when UVarSet.mem x blacklist |> not ->
      blacklist, UVarSet.add x acc
    | tp -> default (blacklist, acc) tp
  in match t with
    | Mono t             -> foldl helper (UVarSet.empty, UVarSet.empty) t |> snd
    | Schema (tp, uvars) -> foldl helper (uvars, UVarSet.empty) tp |> snd

let generalize env_uvars tp =
  let tp_uvars  = get_uvars (typ_mono tp) in
  let diff = UVarSet.diff tp_uvars env_uvars in
  typ_schema diff tp

