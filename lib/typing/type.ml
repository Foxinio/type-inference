open Core.Imast
open Core

(** Internal representation of types *)
module UVar = Tvar.Make()
module TVar = Tvar.Make()
module TVarSet = TVar.MakeSet()
module TVarMap = TVar.MakeMap()

module Level = struct
  type t = int * int
  let starting = 0, 0
  let increase_minor (major,minor) = (major,minor+1)
  let increase_major (major,minor) = (major+1,0)
  let compare_major (major1,_) (major2,_) = compare major1 major2
  let compare a b =
    match compare_major a b with
    | 0 -> compare (snd a) (snd b)
    | n -> n
end

type t =
  | TIUnit
  | TIEmpty
  | TIBool
  | TIInt
  | TIVar    of TVar.t
  | TIADT    of IMAstVar.t * Level.t * t list
  | TIUVar   of uvar
  | TIArrow  of t list * t
  | TIProd   of t list

and uvar_value =
  | Realised of t
  | Unrealised of Level.t

and uvar_struct = {
  id: UVar.t;
  value: uvar_value;

  (* gvar set means that it was created in abstraction application,
   *   is an arrow and can be generalised to arrow that takes more arguments.
   *
   * (τ1, τ2) -> (τ3, τ4) -> τ5
   *    =>
   * (τ1, τ2, τ3, τ4) -> τ5
   *)
  is_gvar: bool;
}
and uvar = uvar_struct ref
and view =
  | TUnit
  | TEmpty
  | TBool
  | TInt
  | TVar    of TVar.t
  | TADT    of IMAstVar.t * Level.t * t list
  | TGVar   of uvar * view option
  | TUVar   of uvar
  | TArrow  of t list * t
  | TProd   of t list

let t_unit  = TIUnit
let t_empty = TIEmpty
let t_bool  = TIBool
let t_int   = TIInt
let t_var x = TIVar x
let t_arrow tps tp2 = TIArrow(tps, tp2)
let t_adt name level tps = TIADT(name, level, tps)
let t_pair tp1 tp2 = TIProd([tp1; tp2])
let t_prod tps     = TIProd(tps)

let makeUvar gvar level =
  { value=Unrealised level; id=UVar.fresh (); is_gvar=gvar; }
let is_gvar {contents={is_gvar;_}} = is_gvar
let set_gvar x v = x := { !x with is_gvar=v }
let id_of_uvar {contents={id;_}} = id

let fresh_uvar level = TIUVar (ref (makeUvar false level))
let fresh_gvar level = TIUVar (ref (makeUvar true level))
let fresh_tvar () = TIVar (TVar.fresh ())

let rec view tp =
  let rec prune_uvar = function
    | TIUVar ({contents={ value=Realised tp;_}} as x) ->
      let shortened = prune_uvar tp in
      x := { !x with value=Realised shortened };
      shortened
    | tp -> tp
  in
  let view_uvar x =
    match !x with
    | {value=Unrealised _; _} -> None
    | {value=Realised tp; _ } ->
      let tp = prune_uvar tp in
      x := { !x with value=Realised tp };
      Some (view tp)
  in
  match tp with
  | TIUVar x when is_gvar x ->
      TGVar (x, view_uvar x)
  | TIUVar ({contents={value=Realised _;_}} as x) ->
      Option.get (view_uvar x)
  | TIUVar ({contents={value=Unrealised _;_}} as x) ->
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
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _
    | TIUVar ({contents={value=Unrealised _;_}}) -> ()
    | TIUVar ({contents={value=Realised tp;_}}) ->
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
  let helper default = function
    | TIUVar ({contents={ value=Unrealised level;_}} as x)
        when Level.compare level' level < 0 ->
      x := { !x with value=Unrealised level' };
    | TIADT (_, level, _) when Level.compare level level' > 0->
      raise (Cannot_compare (tp, (TIUVar x)))
    | tp -> default tp
  in iter helper tp

(* Join operation
 * (τ₁, τ₂) -> (τ₃) -> τ₄
 *    ⊔
 * (τ₁) -> (τ₂, τ₃) -> τ₄
 *    =>
 * (τ₁) -> (τ₂) -> (τ₃) -> τ₄
 *
 *)
and join (new_tp : t) (current_tp : t) =
  (* TODO: make sure this is correct *)
  (* this is not correct, because all we know is that overhead uvar can be generalised,
     however we know nothing about uvar at this stage
   *)
  (* begin match new_tp, current_tp with *)
  (*   | TIUVar x, TIUVar y when is_gvar x || is_gvar y -> *)
  (*     set_gvar x true; *)
  (*     set_gvar y true *)
  (*   | _ -> () *)
  (* end; *)
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

  | TIProd(ts1), TIProd(ts2) when List.length ts1 = List.length ts2 ->
      TIProd (List.map2 join ts1 ts2)
  | TIProd _, _ -> raise (Cannot_compare (new_tp, current_tp))

and join_arrows (tpsa, resa) (tpsb, resb) =
  match tpsa, tpsb with
  | tpa :: tpsa, tpb :: tpsb ->
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



let t_of_uvar { contents={value;_} } = value
let uvar_compare { contents={id=id1;_}} { contents={id=id2;_}} = UVar.compare id1 id2

module UVarSet = Set.Make(struct
  type t = uvar
  let compare = uvar_compare
end)



let rec fold_map f init =
  let default acc t = match t with
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _ | TIUVar ({contents={value=Unrealised _;_}}) -> acc, t
    | TIUVar ({contents={value=Realised tp;_}} as x) ->
      let acc, tp = fold_map f acc tp in
      set_uvar x tp;
      acc, TIUVar x
    | TIADT (name, lvl, tps) ->
      let acc, tps = List.fold_left_map (fold_map f) acc tps in
      acc, TIADT (name, lvl, tps)
    | TIArrow (tps, tp) ->
      let acc, tps = List.fold_left_map (fold_map f) acc tps in
      let acc, tp = fold_map f acc tp in
      acc, TIArrow (tps, tp)
    | TIProd tps ->
      let acc, tps = List.fold_left_map (fold_map f) acc tps in
      acc, TIProd tps
  in
  f default init



let rec map f : t -> t =
  let default t = match t with
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _ | TIUVar ({contents={value=Unrealised _;_}}) -> t
    | TIUVar ({contents={value=Realised tp;_}} as x) ->
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
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _ | TIUVar ({contents={value=Unrealised _;_}}) -> init
    | TIADT (_, _, tps) ->
      List.fold_right (foldr f) tps init
    | TIUVar ({contents={value=Realised tp;_}}) ->
      f default (foldr f tp init) tp
    | TIProd tps ->
      List.fold_right (foldr f) tps init
    | TIArrow (tps, tp) ->
      f default (List.fold_right (foldr f) tps init) tp
  in
  f default (foldr f t init) t

let rec foldl f init t =
  let rec default init t = match t with
    | TIUnit | TIEmpty | TIBool | TIInt | TIVar _ | TIUVar ({contents={value=Unrealised _;_}}) -> init
    | TIADT (_, _, tps) ->
      List.fold_left (foldl f) init tps
    | TIUVar ({contents={value=Realised tp;_}}) ->
      foldl f (f default init tp) tp
    | TIProd tps ->
      List.fold_left (foldl f) init tps
    | TIArrow (tps, tp) ->
      List.fold_left (foldl f) (f default init tp) tps
  in
  foldl f (f default init t) t

let degeneralize_uvars tp =
  let rec helper default = function
    | TIUVar {contents={value=Realised tp;_}} -> helper default tp
    | TIUVar ({contents={value=Unrealised _;_}} as x) ->
      x := { !x with is_gvar=false };
      TIUVar x
    | tp -> default tp in
  map helper tp

type typ =
  | Mono of t
  | Schema of t * TVarSet.t

let typ_mono t = Mono t
let typ_schema set t = Schema (t, set)

let get_arguments = function
  | Mono _ -> TVarSet.empty
  | Schema (_, set) -> set

let get_template = function
  | Mono t -> t
  | Schema (t, _) -> t

let instantiate ?(mapping=TVarMap.empty) level = function
  | Mono tp -> tp
  | Schema (tp, tvars) ->
      let tvars_seq =
        TVarSet.to_seq tvars |>
        Seq.filter (fun x -> TVarMap.mem x mapping |> not) |>
        Seq.flat_map (fun x -> Seq.return (x, fresh_uvar level)) in
      let mapper = TVarMap.add_seq tvars_seq mapping in
      let instantiate default tp = match tp with
        | TIVar x ->
            TVarMap.find_opt x mapper |> Option.value ~default:tp
        | tp -> default tp
      in map instantiate tp

let generalize accepted_level tp =
  let module UVartbl = UVar.MakeHashtbl() in
  let mapper = UVartbl.create 11 in
  let lookup x =
    match UVartbl.find_opt mapper x with
    | Some x -> x
    | None   ->
      let v = TVar.fresh () in
      UVartbl.add mapper x v;
      v
  in
  let rec helper default tp = match tp with
    | TIUVar ({contents={value=Realised _; is_gvar=true; _}} as x) ->
      set_gvar x false;
      helper default tp
    | TIUVar ({contents={value=Unrealised level;_}} as x)
        when Level.compare_major level accepted_level = 0 ->
      TIVar (lookup (id_of_uvar x))
    | tp -> default tp
  in 
  let tp = map helper tp in
  let lst = UVartbl.to_seq mapper |> Seq.unzip |> snd |> TVarSet.of_seq in
  Schema (tp, lst)


