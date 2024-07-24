module IMAstVar = Var.Make()

include Ast.Make(struct
  type t = IMAstVar.t
end)

module VarMap = IMAstVar.MakeMap()
module VarSet = IMAstVar.MakeSet()
module VarTbl
: sig
  include module type of IMAstVar.MakeHashtbl()
  val gen_name : unit -> string
end = struct
  include IMAstVar.MakeHashtbl()
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

type program = expl_type expr * string VarTbl.t

