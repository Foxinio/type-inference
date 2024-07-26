type t = int * int * int

let starting = 0, 0, 0

let increase_minor (major,minor, eff) = major,minor+1, eff
let increase_major (major,minor, eff) = major+1,0, eff

let compare_major (major1,_,_) (major2,_,_) = compare major1 major2

let compare (major1,minor1,_) (major2,minor2,_) =
  let cmp = compare major1 major2 in
  if cmp = 0
  then compare minor1 minor2
  else cmp

let to_string (major,minor,eff) = string_of_int major ^ "."
  ^ string_of_int minor
