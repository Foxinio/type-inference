(** Abstract syntax tree of a parsed program *)

type ('expr, 'typ) node = {
  data      : 'expr;
  typ       : 'typ;
  start_pos : Lexing.position;
  end_pos   : Lexing.position
}

module Make(VarType : sig type t end) = struct

  type var_type = VarType.t

  type      var_name  = var_type
  type 'typ var_def   = var_type * 'typ
  type      ctor_name = var_type
  type 'typ ctor_def  = ctor_name * 'typ
  type      alias     = var_type * var_type list 

  type 'typ expr = ('typ expr_data, 'typ) node
  and 'typ expr_data =
    | EUnit
    | EBool   of bool
    | ENum    of int
    | EVar    of var_name * 'typ list
    | EExtern of string  * Effect.t * 'typ
    | EFn     of 'typ var_def * 'typ expr
    | EFix    of 'typ var_def * 'typ var_def * 'typ expr
    | EApp    of 'typ expr * 'typ expr
    | ELet    of 'typ var_def * 'typ expr * 'typ expr
    | EPair   of 'typ expr * 'typ expr
    | EFst    of 'typ expr
    | ESnd    of 'typ expr
    | EIf     of 'typ expr * 'typ expr * 'typ expr
    | ESeq    of 'typ expr * 'typ expr
    | ETypeAlias of alias * 'typ * 'typ expr
    | EType   of alias * 'typ ctor_def list * 'typ expr
    | ECtor   of ctor_name * 'typ list * 'typ expr
    | EMatch  of 'typ expr * 'typ clause list

  and 'typ clause = ctor_name * 'typ var_def * 'typ expr

  type expl_type =
    | TUnit
    (* this hole means there was a gap in type given by the user *)
    | THole
    | TInt
    | TBool
    | TVar of var_type
    | TAlias of var_type * expl_type list
    | TPair of expl_type * expl_type
    | TArrow of expl_type * expl_type

  let pp_expl_type string_of_name =
    let rec inner lvl = function
      | TUnit -> "unit"
      | THole -> "_"
      | TInt -> "int"
      | TBool -> "bool"
      | TVar name -> string_of_name name
      | TAlias (name, tps) ->
        let strs = List.map (inner 1) tps |> String.concat ", " in
        string_of_name name ^ "<" ^ strs ^ ">"
      | TPair (tp1, tp2) ->
        "(" ^ inner 3 tp1 ^ " * " ^ inner 3 tp2 ^ ")"
        |> at_lvl lvl 2
      | TArrow (tparg, tpres) ->
        "(" ^ inner 1 tparg ^ " -> " ^ inner 0 tpres ^ ")"
        |> at_lvl lvl 0
    and at_lvl l1 l2 str =
      if l1 > l2 then Printf.sprintf "(%s)" str
      else str
    in inner 0


  let t_arrow targs tres =
    assert (not @@ List.is_empty targs);
    List.fold_right (fun arg res -> TArrow (arg, res)) targs tres

  let string_of_expr e string_of_name string_of_typ =
    let rec string_of_data data typ =
      match data with
      | EUnit -> "EUnit"
      | EBool b  -> "EBool "^string_of_bool b
      | ENum n  -> "ENum "^string_of_int n
      | EVar (x,tps)  -> "EVar "^string_of_var (x,tps)^" : "^string_of_typ typ
      | EExtern (name, _, _)  -> "EExtern "^name
      | EFn (x, e) ->
        "EFn "^string_of_var_def x^" : "^string_of_typ e.typ^" => "^aux e
      | EFix (f, x, e)  ->
        "EFix "^string_of_var_def f^" "^string_of_var_def x^" : "^string_of_typ e.typ^" => "^aux e
      | EApp (e1, e2)  -> "EApp "^aux e1^" "^aux e2^" : "^string_of_typ typ
      | ELet (x, e1, e2)  -> "ELet "^string_of_var_def x^" "^aux e1^"\n"^aux e2
      | EPair (e1, e2)  -> "EPair "^aux e1^" "^aux e2
      | EFst e  -> "EFst "^aux e
      | ESnd e  -> "ESnd "^aux e
      | EIf (e1, e2, e3)  -> "EIf : ("^string_of_typ typ^") "^aux e1^" "^aux e2^" "^aux e3
      | ESeq (e1, e2)  -> "ESeq "^aux e1^" "^aux e2
      | ETypeAlias (_, _, e) -> "ETypeAlias "^aux e
      | EType (_, _, e) -> "EType "^aux e
      | ECtor (name, tps, e) ->
        let tps' = List.map string_of_typ tps |> String.concat ", " in
        "ECtor "^string_of_name name^" ["^tps'^"]: ("^string_of_typ typ^") "^aux e
      | EMatch (e, cl) ->
        let clauses = List.map aux_clause cl |> String.concat " " in
        "EMatch : ("^string_of_typ typ^") "^aux e^" "^clauses
    and aux_clause (ctor_name, var, e) =
      "("^string_of_name ctor_name^" "
         ^string_of_var_def var^" => "^aux e^")"
    and string_of_var_def (x,tp) =
      "("^string_of_name x^" : "^string_of_typ tp^")"
    and string_of_var (x,tps) =
      let strs = List.map string_of_typ tps |> String.concat ", " in
        "("^string_of_name x^" [" ^ strs ^ "])"
    and aux e = "("^string_of_data e.data e.typ^")"
    in aux e
end


include Make(struct
  type t = string
end)


type program = expl_type expr


(* ######################################################################### *)
(* TESTS *)


let%test_module "Core.Ast Testing module" =
  (module struct

  let%test "t_arrow test: test fail on empty input" =
    let targs = [] in
    let tres = TBool in
    try
      ignore @@ t_arrow targs tres;
      false
    with Assert_failure _ -> true

  let cmp a = function
    | TAlias(b, _) -> String.equal a b
    | _ -> false

  let rec unfold_arrow = function
    | TArrow(t1, t2) ->
      let lst, t2 = unfold_arrow t2 in
      t1::lst, t2
    | t -> [], t

  let corr_args = ["x1"; "x2"; "x3"]
  let targs = List.map (fun x -> TAlias(x,[])) corr_args
  let tres = TBool

  let%test "t_arrow test: test correct argument order" =
    let typ = t_arrow targs tres in
    let targs', tres' = unfold_arrow typ in
    List.for_all2 cmp corr_args targs' && tres' = tres

end)
