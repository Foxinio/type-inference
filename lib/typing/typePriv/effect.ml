(* LICENSE *)
include Core.Effect

module EffVar = Core.Var.Make()

type uvar = uvar_value ref * EffVar.t
and uvar_value =
  | Const of t
  | Unknown of Level.t
  | Link of uvar

let fresh_uvar lvl =
  ref (Unknown lvl), EffVar.fresh()

let follow_link x =
  let module Set = EffVar.MakeSet() in
  let rec follow_link seen (v,id as x) =
    if Set.mem id seen then failwith "loop in eff uvars" else
    let seen = Set.add id seen in
    match !v with
    | Link y ->
      let res = follow_link seen y in
      v := Link res;
      res
    | _ -> x
  in follow_link Set.empty x

let rec view (v,_ as x) =
  match !v with
  | Unknown _ -> EffUnknown
  | Const eff -> eff
  | Link _ ->
    let y = follow_link x in
    v := Link y;
    view y

let unwrap (x,_) = !x

let set_uvar (x,_) v =
  match !x with
  | Link _ -> failwith "tried to set linked eff uvar"
  | _ -> x := Const v

let link_uvar (x,_) y =
  match !x with
  | Const _ -> failwith "tried to link constant eff uvar"
  | _ -> x := Link y

let ( ! ) = view

let compare a b = compare !a !b

let wrap_uvar lvl eff =
  let uv = fresh_uvar lvl in
  set_uvar uv eff;
  uv

let copy_uvar lvl uv =
  let res = fresh_uvar lvl in
  set_uvar res !uv;
  res

let is_impure a =
  match view a with
  | EffImpure -> true
  | _ -> false

module EffUvMap = Map.Make(struct
  type t = uvar
  let compare (_, id1) (_, id2) = EffVar.compare id1 id2
end)

module EffUvSet = Set.Make(struct
  type t = uvar
  let compare (_, id1) (_, id2) = EffVar.compare id1 id2
end)

module EffUvTbl = Hashtbl.Make(struct
  type t = uvar
  let equal (_, id1) (_, id2) = EffVar.compare id1 id2 = 0
  let hash (_, id) = EffVar.hash id
end)
