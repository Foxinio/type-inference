open Main
open Uvar
open Type_visitors
module EffUvSet = Effect.EffUvSet
module EffUvMap = Effect.EffUvMap
module EffUvTbl = Effect.EffUvTbl

let id_of_uvar {contents={id;_}} = id

type typ =
  | Mono of t
  | Schema of t * TVarSet.t * EffUvSet.t

let typ_mono t = Mono t
let typ_schema set t = Schema (t, set, EffUvSet.empty)

let get_arguments = function
  | Mono _ -> TVarSet.empty
  | Schema (_, set, _) -> set

let get_template = function
  | Mono t -> t
  | Schema (t, _, _) -> t

let instatitate_schema mapping level (tp : t) tvars effvars =
    let tvars_seq = TVarSet.to_seq tvars
      |> Seq.filter (fun x -> TVarMap.mem x mapping |> not)
      |> Seq.map (fun x -> x, Uvar.fresh_uvar level) in
    let effmapper = EffUvSet.to_seq effvars
      |> Seq.map (fun x -> x, Effect.fresh_uvar level)
      |> EffUvMap.of_seq in
    let mapper = TVarMap.add_seq tvars_seq mapping in
    let rec instantiate default tp = match tp with
      | TVar x ->
          TVarMap.find_opt x mapper |> Option.value ~default:tp
      | TArrow (eff, arg, res) when EffUvMap.mem eff effmapper ->
          let eff' = EffUvMap.find eff effmapper in
          let arg = instantiate default arg in
          let res = instantiate default res in
          TArrow(eff', arg, res)
      | tp -> default tp
    in map instantiate tp

let instantiate ?(mapping=TVarMap.empty) level = function
  | Mono tp -> tp
  | Schema (tp, tvars, effvars) ->
    instatitate_schema mapping level tp tvars effvars

let generalize accepted_level tp =
  let module UVartbl = UVar.MakeHashtbl() in
  let uvmapper = UVartbl.create 11 in
  let effmapper = EffUvTbl.create 11 in
  let lookup_eff x =
    match EffUvTbl.find_opt effmapper x with
    | Some x -> x
    | None   ->
      let res = Effect.follow_link x in
      begin match Effect.unwrap res with
      | Unknown _ ->
        EffUvTbl.add effmapper x res;
        res
      | Const _ -> x
      | Link _ -> assert false
      end
  and lookup_uv x =
    match UVartbl.find_opt uvmapper x with
    | Some x -> x
    | None   ->
      let v = TVar.fresh () in
      UVartbl.add uvmapper x v;
      v
  in
  let rec helper default tp =
    let open Effect in
    match tp with
    | TUVar ({contents={value=Unrealised level;_}} as x)
        when Level.compare_major level accepted_level = 0 ->
      TVar (lookup_uv (id_of_uvar x))
    | TArrow (eff, arg, res) when !eff = EffUnknown ->
      let eff' = lookup_eff eff in
      let arg' = helper default arg in
      let res' = helper default res in
      TArrow(eff', arg', res')
    | tp -> default tp
  in 
  let tp = map helper tp in
  let uvset  = UVartbl.to_seq_values uvmapper |> TVarSet.of_seq in
  let effset = EffUvTbl.to_seq_values effmapper |> EffUvSet.of_seq in
  Schema (tp, uvset, effset)
