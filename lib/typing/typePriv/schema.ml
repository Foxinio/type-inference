open Main
open Uvar
open Type_visitors

let id_of_uvar {contents={id;_}} = id

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

let instatitate_schema mapping level (tp : t) tvars =
    let tvars_seq = TVarSet.to_seq tvars
      |> Seq.filter (fun x -> TVarMap.mem x mapping |> not)
      |> Seq.map (fun x -> x, Uvar.fresh_uvar level) in
    let mapper = TVarMap.add_seq tvars_seq mapping in
    let instantiate default tp = match tp with
      | TVar x ->
          TVarMap.find_opt x mapper |> Option.value ~default:tp
      | tp -> default tp
    in map instantiate tp

let instantiate ?(mapping=TVarMap.empty) level = function
  | Mono tp -> tp
  | Schema (tp, tvars) ->
    instatitate_schema mapping level tp tvars

let generalize accepted_level tp =
  let module UVartbl = UVar.MakeHashtbl() in
  let uvmapper = UVartbl.create 11 in
  let lookup_uv x =
    match UVartbl.find_opt uvmapper x with
    | Some x -> x
    | None   ->
      let v = TVar.fresh () in
      UVartbl.add uvmapper x v;
      v
  in
  let helper default tp =
    let open Effect in
    match tp with
    | TUVar ({contents={value=Unrealised level;_}} as x)
        when Level.compare_major level accepted_level = 0 ->
      TVar (lookup_uv (id_of_uvar x))
    | tp -> default tp
  in 
  let tp = map helper tp in
  let uvset  = UVartbl.to_seq_values uvmapper |> TVarSet.of_seq in
  Schema (tp, uvset)
