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

let instantiate ?(mapping=TVarMap.empty) level = function
  | Mono tp -> tp
  | Schema (tp, tvars) ->
      let tvars_seq =
        TVarSet.to_seq tvars |>
        Seq.filter (fun x -> TVarMap.mem x mapping |> not) |>
        Seq.flat_map (fun x -> Seq.return (x, fresh_uvar level)) in
      let mapper = TVarMap.add_seq tvars_seq mapping in
      let instantiate default tp = match tp with
        | TVar x ->
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
  let helper default tp = match tp with
    | TUVar ({contents={value=Unrealised level;_}} as x)
        when Level.compare_major level accepted_level = 0 ->
      TVar (lookup (id_of_uvar x))
    | tp -> default tp
  in 
  let tp = map helper tp in
  let lst = UVartbl.to_seq mapper |> Seq.unzip |> snd |> TVarSet.of_seq in
  Schema (tp, lst)
