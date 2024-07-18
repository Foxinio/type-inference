(** Abstract syntax tree of a parsed program *)

(** Node of AST, that contains additional information about the location,
  *   and optionally type if it was given by user                         *)

type ('expr, 'typ) node = {
  data      : 'expr;
  typ       : 'typ;
  start_pos : Lexing.position;
  end_pos   : Lexing.position
}

module Make(VarType : sig type t end) = struct

  type var_type = VarType.t

  type 'typ var       = var_type * 'typ
  type      ctor_name = var_type
  type 'typ ctor_def  = ctor_name * 'typ
  type      alias     = var_type * var_type list 

  type 'typ expr = ('typ expr_data, 'typ) node
  and 'typ expr_data =
    | EUnit
    | EBool   of bool
    | ENum    of int
    | EVar    of 'typ var
    | EExtern of string  * Effect.t * 'typ * 'typ
    | EFn     of 'typ var * 'typ expr
    | EFix    of 'typ var * 'typ var * 'typ expr
    | EApp    of 'typ expr * 'typ expr
    | ELet    of 'typ var * 'typ expr * 'typ expr
    | EPair   of 'typ expr * 'typ expr
    | EFst    of 'typ expr
    | ESnd    of 'typ expr
    | EIf     of 'typ expr * 'typ expr * 'typ expr
    | ESeq    of 'typ expr * 'typ expr
    | ETypeAlias of alias * 'typ * 'typ expr
    | EType   of alias * 'typ ctor_def list * 'typ expr
    (* ECtor is equivalent to EFold *)
    | ECtor   of ctor_name * 'typ expr
    (* EMatch is equivalent to EUnfold *)
    | EMatch  of 'typ expr * 'typ clause list

  and 'typ clause = ctor_name * 'typ var * 'typ expr

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

  let t_arrow targs tres =
    assert (not @@ List.is_empty targs);
    List.fold_right (fun t1 t2 ->
      TArrow (t1, t2)) (List.tl targs)
      (TArrow (List.hd targs, tres))

  let rec type_fmap f t =
    let default t = match t with
      | TUnit | THole | TInt | TBool | TVar _ -> t
      | TAlias (name, tps) ->
        TAlias (name, List.map (type_fmap f) tps)
      | TPair (tp1, tp2) ->
        TPair (type_fmap f tp1, type_fmap f tp2)
      | TArrow (tparg, tpres) ->
        TArrow (type_fmap f tparg, type_fmap f tpres)
    in
    f default t

  let rec type_iter f t =
    let default t = match t with
      | TUnit | THole | TInt | TBool | TVar _ -> ()
      | TAlias (_, tps) ->
        List.iter (type_iter f) tps
      | TPair (tp1, tp2) ->
        type_iter f tp1;
        type_iter f tp2
      | TArrow (tparg, tpres) ->
        type_iter f tparg;
        type_iter f tpres
    in
    f default t

  (** The same way fold_right starts from the end of the list and makes it way outside,
        `fold_right f [a1; ...; an] init` is `f a1 (f a2 (... (f an init) ...))`
      foldr on trees works bottom-up. Not tail-recursive.
      *)
  let rec type_foldr f t init =
    let rec default t = match t with
      | TUnit | THole | TInt | TBool | TVar _ -> init
      | TAlias (name, tps) ->
        List.fold_right (type_foldr f) tps init
      | TPair (tp1, tp2) ->
        f default (f default init tp1) tp2
      | TArrow (tparg, tpres) ->
        f default (type_foldr f tparg init) tpres
    in
    f default (type_foldr f t init) t

  (** The same way fold_left starts from the begining of the list and makes it way inside,
        `fold_left f init [b1; ...; bn]` is `f (... (f (f init b1) b2) ...) bn`
      foldl on trees works top-down.
      *)
  let rec type_foldl f init t =
    let rec default t = match t with
      | TUnit | THole | TInt | TBool | TVar _ -> init
      | TAlias (name, tps) ->
        List.fold_left (type_foldl f) init tps
      | TPair (tp1, tp2) ->
        type_foldl f (f default init tp1) tp2
      | TArrow (tparg, tpres) ->
        type_foldl f (f default init tpres) tparg
    in
    type_foldl f (f default init t) t
end


include Make(struct
  type t = string
end)


type program = expl_type expr
