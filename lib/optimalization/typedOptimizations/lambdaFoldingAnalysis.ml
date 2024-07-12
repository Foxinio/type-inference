(**
  * LICENSE
  *)

open SystemF


module FoldingConstraint =
struct
  
Worklist.Constraint(struct
  type t = unit
end)

end

let rec generate_constraints (p:program) =
  
