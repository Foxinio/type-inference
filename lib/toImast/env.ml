open Core
open Imast
open Main

module StringMap = Map.Make(String)

type t =
  { gamma : var_type StringMap.t
  ; delta : var_type StringMap.t
  ; ctors : var_type StringMap.t
  }

let empty = 
  { gamma=StringMap.empty
  ; delta=StringMap.empty
  ; ctors=StringMap.empty
  }

let add_var ({gamma;_} as env) x v =
  { env with gamma=StringMap.add x v gamma}

let add_tvar ({delta;_} as env) x v =
  { env with delta=StringMap.add x v delta}


let extend_delta ({delta;_} as env) (keys : string list) : t * var_type list =
  let f x =
    let v = VarTbl.fresh_var x in
    ((x,v),v)
  in
  let lst = List.map f keys |> List.split in
  {env with delta=StringMap.add_seq (fst lst |> List.to_seq) delta},
  snd lst

let extend_ctors ({ctors;_} as env) ctor_list =
    let f (ctor_name, ctor_type) = 
      let ctor_name' = VarTbl.fresh_var ctor_name in
      ((ctor_name, ctor_name'),
       (ctor_name', ctor_type))
    in
  let lst = List.map f ctor_list |> List.split in
  {env with ctors=StringMap.add_seq (fst lst |> List.to_seq) ctors},
  snd lst

let lookup_tvar {delta;_} e x =
  match StringMap.find_opt x delta with
  | Some v -> v
  | None -> raise (Out_of_scope (x, e))

let lookup_var {gamma;_} e x =
  match StringMap.find_opt x gamma with
  | Some v -> v
  | None -> raise (Out_of_scope (x, e))

let lookup_ctor {ctors;_} e ctor =
  match StringMap.find_opt ctor ctors with
  | Some v -> v
  | None -> raise (Out_of_scope (ctor, e))
