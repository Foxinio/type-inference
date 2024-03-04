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
  | TIScheme of Imast.IMAstVar.t * t list
  | TIGVar   of uvar
  | TIUVar   of uvar
  | TIArrow  of t list * t
  | TIProd   of t list

and uvar = (t option * UVar.t) ref
and view =
  | TUnit
  | TEmpty
  | TBool
  | TInt
  | TVar    of Imast.IMAstVar.t
  | TScheme of Imast.IMAstVar.t * t list
  | TGVar   of uvar * view option
  | TUVar   of uvar
  | TArrow  of t list * t
  | TProd   of t list

let fresh_uvar () = TIUVar (ref (None, UVar.fresh ()))
let fresh_gvar () = TIGVar (ref (None, UVar.fresh ()))

let t_unit  = TIUnit
let t_empty = TIEmpty
let t_bool  = TIBool
let t_int   = TIInt
let t_var x = TIVar (x, false)
let t_arrow  tps tp2 = TIArrow(tps, tp2)
let t_scheme name tps = TIScheme(name, tps)
let t_pair   tp1 tp2 = TIProd([tp1; tp2])
let t_prod   tps = TIProd(tps)

let rec t_of_view = function
  | TUVar x -> TIUVar x
  | TGVar (x, _) -> TIGVar x
  | TVar x -> TIVar (x, false)
  | TScheme(x, tps) -> TIScheme(x, tps)
  | TUnit -> TIUnit
  | TEmpty -> TIEmpty
  | TBool -> TIBool
  | TInt -> TIInt
  | TArrow(tps, tp2) -> TIArrow(tps, tp2)
  | TProd tps -> TIProd tps

let rec view tp =
  let view_uvar x =
    match !x with
    | None, _ -> None
    | Some tp, i ->
      let tp = view tp in
      x := Some (t_of_view tp), i;
      Some tp
  in
  match tp with
  | TIUVar ({contents=Some(_),_} as x) ->
      Option.get (view_uvar x)
  | TIUVar ({contents=None,_} as x) ->
      TUVar x
  | TIGVar x ->
      TGVar (x, view_uvar x)
  | TIVar (x, _) -> TVar x
  | TIScheme(x, tps) -> TScheme(x, tps)
  | TIUnit -> TUnit
  | TIEmpty -> TEmpty
  | TIBool -> TBool
  | TIInt -> TInt
  | TIArrow(tps, tp2) -> TArrow(tps, tp2)
  | TIProd tps -> TProd tps


exception Cannot_compare of t * t

let rec set_uvar_int x tp general =
  match !x with
  | None, i -> x := Some tp, i
  | Some tp_current, i when general ->
      let res = reconstruct tp tp_current in
      x := Some res, i
  | Some _, i -> assert false

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
    | None, i ->
        x := Some tp, i;
        tp
    | Some tp, i ->
        let res = fn tp in
        x := Some res, i;
        res
  in
  match new_tp, currrnet_tp with
  | TIUVar x, _ ->
      uvar_map x currrnet_tp (fun _ -> raise (Cannot_compare (new_tp, currrnet_tp)))
  | TIGVar x, _ ->
      uvar_map x currrnet_tp (fun tp -> reconstruct tp currrnet_tp)
  | _, TIUVar x ->
      uvar_map x new_tp (fun _ -> raise (Cannot_compare (new_tp, currrnet_tp)))
  | _, TIGVar x ->
      uvar_map x new_tp (fun tp -> reconstruct new_tp tp)

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


let set_uvar x tp =
  set_uvar_int x tp false
let set_gvar x tp =
  set_uvar_int x tp true
let t_of_uvar { contents=x,_ } = x
let uvar_compare { contents=_,x } { contents=_,y } = UVar.compare x y

module UVarSet = Set.Make(struct
  type t = uvar
  let compare = uvar_compare
end)

module UVarMap = Map.Make(struct
  type t = uvar
  let compare = uvar_compare
end)



type typ =
  | Mono of t
  | Schema of t * UVarSet.t

let typ_mono t = Mono t
let typ_schema t set = Schema (t, set)

let instantiate ?(mapping=UVarMap.empty) = function
  | Mono tp -> tp
  | Schema (tp, uvars) ->
      let uvars_seq =
        UVarSet.to_seq uvars |>
        Seq.filter (fun x -> UVarMap.mem x mapping |> not) |>
        Seq.flat_map (fun x -> Seq.return (x, fresh_uvar ())) in
      let mapper = UVarMap.add_seq uvars_seq mapping in
      let rec instantiate = function
        | TIUVar (x) ->
            UVarMap.find_opt x mapper |> Option.value ~default:(TIUVar x)
        | TIGVar (x) ->
            UVarMap.find_opt x mapper |> Option.value ~default:(TIGVar x)
        | TIArrow (tps, tp2) ->
            let tp1 = List.map instantiate tps in
            let tp2 = instantiate tp2 in
            TIArrow (tp1, tp2)
        | TIProd tps ->
            TIProd (List.map instantiate tps)
        | tp -> tp
      in instantiate tp

let get_uvars t =
  let rec inner set t =
    let fold_fun acc tp = inner set tp |> UVarSet.union acc in
    match view t with
    | TGVar (x, None)
    | TUVar (x)
        when UVarSet.mem x set -> UVarSet.singleton x
    | TUnit | TEmpty | TBool | TInt | TVar _ | TGVar (_, None) | TUVar _ -> UVarSet.empty
    | TGVar (_, Some tp) -> inner set (t_of_view tp)
    | TArrow (tps, tp2) -> UVarSet.union (List.fold_left fold_fun UVarSet.empty tps) (inner set tp2)
    | TScheme (_, tps) -> List.fold_left fold_fun UVarSet.empty tps
    | TProd tps ->
        List.fold_left fold_fun UVarSet.empty tps
  in match t with
  | Mono t -> inner UVarSet.empty t
  | Schema (tp, uvars) ->
      inner uvars tp

let generalize env_uvars tp =
  let tp_uvars  = get_uvars (typ_mono tp) in
  let diff = UVarSet.diff tp_uvars env_uvars in
  typ_schema tp diff

