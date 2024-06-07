(* Ast data definitions and helper functions *)

type ('a,'extra) node = {
  data : 'a;
  extra : 'extra;
}

let make data = { data; extra=() }


type 'extra expr = ('extra expr_data, 'extra) node
and 'extra expr_data =
  | EUnit



type 'a program = 'a expr

let unimplemented () = failwith "unimplemented"
