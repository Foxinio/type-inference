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

  let counter = ref 0
  let gen_name () =
    let name = "#" ^ Utils.gen_name !counter in
    incr counter;
    name

  module VarTbl = IMAstVar.MakeHashtbl()
  type t = string VarTbl.t

  let instance : t = VarTbl.create 411

  let find x =
    match VarTbl.find_opt instance x with
    | Some v -> v
    | None ->
      let name = gen_name () in
      VarTbl.add instance x name;
      name

  let find = VarTbl.find instance

  let add = VarTbl.add instance

  let to_seq () = VarTbl.to_seq instance

  let fresh_var x =
    let v = IMAstVar.fresh () in
    add v x;
    v

end

type program = expl_type expr

let pp_program p =
  let string_of_var = VarTbl.find in
  let string_of_type = pp_expl_type string_of_var in
  string_of_expr p string_of_var string_of_type
