(* ========================================================================== *)

open Erase

let unimplemented () = failwith "unimpelemnted"

let make _ data = { data; extra=() }

let rec clear (e : ('a expr)) : unit expr =
  match e.data with
	| EUnit   -> make e EUnit
	| EBool b -> make e (EBool b)
	| ENum n  -> make e (ENum n)
	| EVar x  -> make e (EVar x)
	| EExtern ex -> make e (EExtern ex)
	| EFn (_, _) -> unimplemented ()
	| EFix (_, _, _) -> unimplemented ()
	| EApp (_, _) -> unimplemented ()
	| ELet (_, _, _) -> unimplemented ()
	| EPair (_, _) -> unimplemented ()
	| EIf (_, _, _) -> unimplemented ()
	| ESeq (_, _) -> unimplemented ()
	| ECtor (_, _) -> unimplemented ()
	| EMatch (_, _) -> unimplemented ()
