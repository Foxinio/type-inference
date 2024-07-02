type t = int * int

let starting = 0, 0

let increase_minor (major,minor) = (major,minor+1)
let increase_major (major,minor) = (major+1,0)

let compare_major (major1,_) (major2,_) = compare major1 major2

let compare a b =
  match compare_major a b with
  | 0 -> compare (snd a) (snd b)
  | n -> n

let to_string (major,minor) = string_of_int major ^ "." ^ string_of_int minor
