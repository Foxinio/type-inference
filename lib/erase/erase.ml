include Ast

let tr_expr e =
  match e with
  | SystemF.EUnit -> make EUnit
  | _ -> unimplemented ()

let tr_program p =
  tr_expr p

let erase_type p =
  tr_program p
