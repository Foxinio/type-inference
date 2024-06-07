
type ('a,'extra) node = {
  data : 'a;
  extra : 'extra;
}


type 'extra expr = ('extra expr_data, 'extra) node
and 'extra expr_data =
  | EUnit



type 'a program = 'a expr

val erase_type : SystemF.program -> unit program
