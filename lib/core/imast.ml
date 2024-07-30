module IMAstVar = Var.Make()

include Ast.Make(struct
  type t = IMAstVar.t
end)

module VarMap = IMAstVar.MakeMap()
module VarSet = IMAstVar.MakeSet()
module VarTbl
: sig
  type t
  val gen_name : unit -> string

  val find : var_type -> string
  val add  : var_type -> string -> unit

  val to_seq : unit -> (var_type*string) Seq.t

  val fresh_var : string -> var_type
end = struct
  module VarTbl = IMAstVar.MakeHashtbl()
  type t = string VarTbl.t

  let instance : t = VarTbl.create 411

  let find = VarTbl.find instance

  let add = VarTbl.add instance

  let to_seq () = VarTbl.to_seq instance

  let fresh_var x =
    let v = IMAstVar.fresh () in
    add v x;
    v

  let counter = ref 0
  let gen_name () =
    let limit = (Char.code 'z') - (Char.code 'a') + 1 in
    let rec inner i =
      if i >= 0 && i < limit then Char.chr i |> String.make 1 
      else
        let minor = i mod limit |> inner
        and major = i / limit |> inner in
        major ^ minor
    in
    let name = "#" ^ inner !counter in
    incr counter;
    name
end

type program = expl_type expr

