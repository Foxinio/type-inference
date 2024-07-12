(* LICENSE *)

type t =
  | EffUnknown
  | EffPure
  | EffImpure

module EffVar = Var.Make()

type uvar = t ref * EffVar.t

let set_uvar ((x,_) : uvar) eff =
  x := eff

let impure_uvar (x,_) =
  x := EffImpure

let get_val (x,_) = !x

let ( ! ) = get_val

let fresh_uvar () : uvar = (ref EffUnknown), EffVar.fresh()

let compare a b =
  match a, b with
  | a, b when a = b -> 0
  | EffUnknown, EffPure -> 1
  | _, EffImpure -> 1
  | a, b -> - compare b a

let join a b =
  match a, b with
  | EffUnknown, eff
  | eff, EffUnknown -> eff
  | EffPure, EffPure -> EffPure
  | EffImpure, _
  | _, EffImpure -> EffImpure

let join_uvar a b =
  let joined = join !a !b in
  set_uvar a joined;
  set_uvar b joined

let uvar_is_impure a =
  match !a with
  | EffImpure -> true
  | _ -> false

let pure = EffPure
let not_pure = EffImpure
let unknown = EffUnknown

let equal_mod_known a b =
  match a,b with
  | _ when a = b -> true
  | EffUnknown, _ | _, EffUnknown -> true
  | _ -> false

let wrap_uvar eff =
  let uv = fresh_uvar () in
  set_uvar uv eff;
  uv

let copy_uvar uv =
  let res = fresh_uvar () in
  set_uvar res !uv;
  res

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
