(** Type inference (for simple types) *)

(** Internal representation of types *)
module Type : sig
  type t
  type uvar

  (** General variable *)
  type gvar
  type uvset
  type view =
    | TUnit
    | TEmpty
    | TBool
    | TInt
    | TUVar    of uvar
    | TGVar    of gvar
    | TArrow   of t * t
    | TPair    of t * t
    | TCoPair  of t * t
  (** list that holds all generalized type variables *)
  (* type schema = gvar list * t *)
    (* | TForallT of SystemF.tvar * t *)
    (*| TForallR of rvar * t*)

  val fresh_uvar : unit -> t
  (* val fresh_gvar : unit -> t *)

  val t_unit    : t
  val t_empty   : t
  val t_bool    : t
  val t_int     : t
  (* val t_gvar    : t *)
  (* val t_var     : SystemF.tvar -> t *)
  val t_arrow   : t -> t -> t
  val t_pair    : t -> t -> t
  val t_copair  : t -> t -> t
  (* val t_forallT : SystemF.tvar -> t -> t *)
  (*val t_forallR : rvar -> t -> t*)

  val view : t -> view

  val set_uvar : uvar -> t -> unit

  (* val uvset_empty : uvset *)
  (* val uvset_diff : uvset -> uvset -> uvset *)
  (* val uvset_fold : (uvar -> 'a -> 'a) -> uvset -> 'a-> 'a *)
  (* val get_fuv_set : t -> uvset *)

end = struct
  type t = 
    | Mono of view
    | Schema of gvar list * view
  and gvar = view option ref
  and uvar = int * t option ref
  and view =
    | TUnit
    | TEmpty
    | TBool
    | TInt
    | TUVar   of uvar
    (* | TVar    of SystemF.tvar *)
    | TGVar    of gvar
    | TArrow  of t * t
    | TPair   of t * t
    | TCoPair of t * t
    (* | TForallT of SystemF.tvar * t *)
    (*| TForallR of rvar * t*)

  module UVSet = Set.Make(struct
      type t = uvar
      let compare (a, _) (b, _) = compare a b
  end)
  type uvset = UVSet.t

  (* module Counter = SystemF. *)

  let fresh_uvar () = 
      let x = ref None in
      Mono (TUVar (1, x))

  let t_unit  = Mono (TUnit)
  let t_empty = Mono (TEmpty)
  let t_bool  = Mono (TBool)
  let t_int   = Mono (TInt)
  (* let t_var v = TVar v *)
  let t_arrow  tp1 tp2 = Mono(TArrow(tp1, tp2))
  let t_pair   tp1 tp2 = Mono(TPair(tp1, tp2))
  let t_copair tp1 tp2 = Mono(TCoPair(tp1, tp2))
  (* let t_forallT v tp = TForallT(v, tp) *)
  (*let t_forallR v tp = TForallR(v, tp)*)

  let rec view tp =
    match tp with
    | Mono (TUVar (i, x)) ->
      begin match !x with
      | None -> TUVar (i,x)
      | Some tp ->
        let tp = view tp in
        x := Some (Mono tp);
        tp
      end
    | Mono (TGVar x) ->
      begin match !x with
      | None -> TGVar x
      | Some tp ->
          tp
      end
    | Mono tp -> tp
    (* here substitute generalized variables for UVars *)
    | Schema (_, tp) -> tp

  let set_uvar (_, x) tp =
    match !x with
    | None -> x := Some tp
    | Some _ -> assert false


  let rec get_fuv_set t = match view t with
    | TUnit | TInt | TEmpty | TBool -> UVSet.empty
    | TUVar x -> UVSet.singleton x
    | TGVar _ -> UVSet.empty
    | TArrow  (tp1, tp2)
    | TPair   (tp1, tp2) 
    | TCoPair (tp1, tp2) -> 
      UVSet.union (get_fuv_set tp1) (get_fuv_set tp2)

  let uvset_empty = UVSet.empty
  let uvset_diff = UVSet.diff
  let uvset_fold = UVSet.fold
end

(* ========================================================================= *)
(* Pretty printing of types *)

(** Creates fresh pretty-printing context *)
let pp_context () = ref []

let pp_at_level l lvl str =
  if lvl > l then Printf.sprintf "(%s)" str
  else str

let rec pp_type ctx lvl tp =
  match Type.view tp with
  | TUnit  -> "Unit"
  | TEmpty -> "Empty"
  | TBool  -> "Bool"
  | TInt   -> "Int"
  | TUVar x ->
    begin match List.assq_opt x !ctx with
    | Some str -> str
    | None ->
      let name = Printf.sprintf "x%d" (List.length !ctx) in
      ctx := (x, name) :: !ctx;
      name
    end
  | TArrow(tp1, tp2) ->
    pp_at_level 0 lvl
      (Printf.sprintf "%s -> %s" (pp_type ctx 1 tp1) (pp_type ctx 0 tp2))
  | TPair(tp1, tp2) ->
    pp_at_level 2 lvl
      (Printf.sprintf "%s * %s" (pp_type ctx 3 tp1) (pp_type ctx 2 tp2))
  | TCoPair(tp1, tp2) ->
    pp_at_level 1 lvl
      (Printf.sprintf "%s + %s" (pp_type ctx 2 tp1) (pp_type ctx 1 tp2))
  | _ -> "(not implemented)"


let string_of_type tp =
    pp_type (pp_context ()) 0 tp

(* let rec subst tsub rsub tp = *)
(*   match Type.view tp with *)
(*   | TUnit | TEmpty | TBool | TInt | TUVar _ -> tp *)
(*   (* | TVar x -> *) *)
(*   (*   begin match SystemF.TVarMap.find_opt x tsub with *) *)
(*   (*   | None    -> tp *) *)
(*   (*   | Some tp -> tp *) *)
(*   (*   end *) *)
(*   | TGVar x -> *)
(*        *)
(*   | TArrow(tp1, tp2) -> *)
(*     Type.t_arrow (subst tsub rsub tp1) (subst tsub rsub tp2) *)
(*   (* | TForallT(a, tp) -> *) *)
(*   (*   let b = SystemF.TVar.fresh () in *) *)
(*   (*   Type.t_forallT b (subst (SystemF.TVarMap.add a (Type.t_var b) tsub) rsub tp) *) *)
(*   (*| TForallR(a, tp) -> *)
(*     let b = RVar.fresh () in *)
(*     TForallR(b, subst tsub (RVarMap.add a ([], Some b) rsub) tp)*) *)
(*   | TPair(tp1, tp2) -> *)
(*     Type.t_pair (subst tsub rsub tp1) (subst tsub rsub tp2) *)
(*   | TCoPair(tp1, tp2) -> *)
(*     Type.t_copair (subst tsub rsub tp1) (subst tsub rsub tp2) *)
(*   (*| TRecord  r -> TRecord  (subst_in_row tsub rsub r) *)
(*   | TVariant r -> TVariant (subst_in_row tsub rsub r)*) *)

(* and subst_in_row tsub rsub (r, re) = *)
(*   let (r', re) = *)
(*     match re with *)
(*     | None -> ([], None) *)
(*     | Some x -> *)
(*       begin match SystemF.RVarMap.find_opt x rsub with *)
(*       | None -> ([], Some x) *)
(*       | Some r -> r *)
(*       end *)
(*   in *)
(*   (List.map (fun (name, tp) -> (name, subst tsub rsub tp)) r @ r', re) *)
(**)
(* let subst_type tp x s = *)
(*   subst (SystemF.TVarMap.singleton x s) SystemF.RVarMap.empty tp *)
(**)
(* let subst_row tp x row = *)
(*   subst SystemF.TVarMap.empty (SystemF.RVarMap.singleton x row) tp *)
(**)




(* ========================================================================= *)
(* Unification *)

exception Cannot_unify

let rec contains_uvar x tp =
  match Type.view tp with
  | TUVar y -> x == y
  | TUnit | TEmpty | TBool | TInt | TGVar _ -> false
  | TArrow(tp1, tp2) | TPair(tp1, tp2) | TCoPair(tp1, tp2) ->
    contains_uvar x tp1 || contains_uvar x tp2
  (* | TForallT (_, tp) -> contains_uvar x tp *)

let unify_with_uvar x tp =
  if contains_uvar x tp then raise Cannot_unify
  else Type.set_uvar x tp

let rec unify tp1 tp2 =
  match Type.view tp1, Type.view tp2 with
  | TUVar x, TUVar y when x == y -> ()
  | TUVar x, _ -> unify_with_uvar x tp2
  | _, TUVar x -> unify_with_uvar x tp1

  (* | TVar x, TVar y when SystemF.TVar.compare x y == 0 -> () *)
  (* | TVar _, _ -> raise Cannot_unify *)

  | TUnit, TUnit -> ()
  | TUnit, _ -> raise Cannot_unify

  | TEmpty, TEmpty -> ()
  | TEmpty, _ -> raise Cannot_unify

  | TBool, TBool -> ()
  | TBool, _ -> raise Cannot_unify

  | TInt, TInt -> ()
  | TInt, _ -> raise Cannot_unify

  | TArrow(ta1, tb1), TArrow(ta2, tb2) ->
    unify ta1 ta2;
    unify tb1 tb2
  | TArrow _, _ -> raise Cannot_unify

  | TPair(ta1, tb1), TPair(ta2, tb2) ->
    unify ta1 ta2;
    unify tb1 tb2
  | TPair _, _ -> raise Cannot_unify

  | TCoPair(ta1, tb1), TCoPair(ta2, tb2) ->
    unify ta1 ta2;
    unify tb1 tb2
  | TCoPair _, _ -> raise Cannot_unify

  (* | TForallT(a1, tp1), TForallT(a2, tp2) -> *)
  (*   let a = SystemF.TVar.fresh () in *)
  (*   unify (subst_type tp1 a1 (Type.t_var a)) (subst_type tp2 a2 (Type.t_var a)) *)
  (* | TForallT _, _ -> raise Cannot_unify *)


(* ========================================================================= *)
(* Type inference *)

(** Typing environments *)
module Env : sig
  type t

  val empty : t

  val extend : t -> Ast.var -> Type.t -> t

  val lookup : t -> Ast.var -> Type.t option
end = struct
  module VarMap = Map.Make(String)

  type t = Type.t VarMap.t

  let empty = VarMap.empty

  let extend env x tp = VarMap.add x tp env

  let lookup env x = VarMap.find_opt x env
end



(* let rec concreate_type tp = match Type.view tp with *)
(*   | TForallT (v, tp) -> *)
(*     let tp' = concreate_type tp in *)
(*     let x, _ = Type.fresh_uvar Type.uvset_empty in *)
(*     subst_type tp' v x *)
(*   | _ -> tp *)

(* type rec_t_ =  *)
(*     | Zero *)
(*     | One of rec_t *)
(*     | Two of rec_t * rec_t *)
(*     | Three of rec_t * rec_t * rec_t *)
(*     | List of rec_t list *)
(* and rec_t = *)
(*     rec_t_ * Ast.expr * Type.t *)

let first (a, _, _) = a
let second (_, a, _) = a
let third (_, _, a) = a

let generalize_type set tp =
    let to_sub = Type.uvset_diff (Type.get_fuv_set tp) set in
    let fn uv lst = 
        let v = SystemF.TVar.fresh () in
        Type.set_uvar uv (Type.t_var v);
        v :: lst in
    let lst = Type.uvset_fold fn to_sub [] in
    let build v tp =
        Type.t_forallT v tp in
    List.fold_right build lst tp

let rec infer_type env set (e : Ast.expr) : rec_t=
  match e.data with
  | EUnit   -> Zero, e, Type.t_unit
  | EBool b -> Zero, e, Type.t_bool
  | ENum  n -> Zero, e, Type.t_int
  | EVar  x ->
    begin match Env.lookup env x with
    | Some tp -> Zero, e, concreate_type tp
    | None ->
      Utils.report_error e "Unbound variable %s" x
    end
  | EFn(x, body) ->
    let tp1, set = Type.fresh_uvar set in
    let (cnt, _, tp2) = infer_type (Env.extend env x tp1) set body in
    One (cnt, body, tp2), e, (Type.t_arrow tp1 tp2)
  | EFix(f, x, body) ->
    let tp1, set = Type.fresh_uvar set in
    let tp2, set = Type.fresh_uvar set in
    let f_tp = Type.t_arrow tp1 tp2 in
    let cnt = check_type (Env.extend (Env.extend env f f_tp) x tp1) body set tp2 in
    One cnt, e, f_tp
  | EApp(e1, e2) ->
    let tp2, set = Type.fresh_uvar set in
    let tp1, set = Type.fresh_uvar set in
    let cnt1 = check_type env e1 set (Type.t_arrow tp2 tp1) in
    let cnt2 = check_type env e2 set tp2 in
    Two (cnt1, cnt2), e, tp1
  | ELet(x, e1, e2) ->
    let cnt1 = infer_type env set e1 in
    let tp1 = generalize_type set (third cnt1) in
    let cnt2 = infer_type (Env.extend env x tp1) set e2 in
    Two(cnt1, cnt2), e, third cnt2
  | EPair(e1, e2) ->
    let cnt1 = infer_type env set e1 in
    let cnt2 = infer_type env set e2 in
    Two(cnt1, cnt2), e, Type.t_pair (third cnt1) (third cnt2)
  | EFst e' ->
    let tp1, set = Type.fresh_uvar set in
    let tp2, set = Type.fresh_uvar set in
    let cnt = check_type env e' set (Type.t_pair tp1 tp2) in
    One(cnt), e, tp1
  | ESnd e' ->
    let tp1, set = Type.fresh_uvar set in
    let tp2, set = Type.fresh_uvar set in
    let cnt = check_type env e' set (Type.t_pair tp1 tp2) in
    One(cnt), e, tp2
  | EInl e' ->
    let (cnt, _, tp1) = infer_type env set e' in
    let tp2, set = Type.fresh_uvar set in
    One (cnt, e', tp1), e, (Type.t_copair tp1 tp2)
  | EInr e' ->
    let tp1, set = Type.fresh_uvar set in
    let (cnt, _, tp2) = infer_type env set e' in
    One (cnt, e', tp2), e, (Type.t_copair tp1 tp2)
  | ECase(e', (x1, e1), (x2, e2)) ->
    let tp1, set = Type.fresh_uvar set in
    let tp2, set = Type.fresh_uvar set in
    let cnt = check_type env e' set (Type.t_copair tp1 tp2) in
    let cnt1 = infer_type (Env.extend env x1 tp1) set e1 in
    let cnt2 = check_type (Env.extend env x2 tp2) e2 set (third cnt1) in
    Three (cnt, cnt1, cnt2), e, (third cnt1)
  | EIf(e1, e2, e3) ->
    let cond_cnt = check_type env e1 set Type.t_bool in
    let true_cnt = infer_type env set e2 in
    let false_cnt = check_type env e3 set (third true_cnt) in
    Three (cond_cnt, true_cnt, false_cnt), e, (third true_cnt)
  | ESeq(e1, e2) ->
    let cnt1 = check_type env e1 set Type.t_unit in
    let cnt2 = infer_type env set e2 in
    let tp = third cnt2 in
    Two(cnt1, cnt2), e, tp
  | EAbsurd e' ->
    let cnt = check_type env e' set Type.t_empty in
    One cnt, e, Type.fresh_uvar Type.uvset_empty |> fst
  | ESelect (e, l) ->
    Utils.report_error e "This language feature is not supported yet!"
  | ERecord _ | ECtor _ | EMatch _ | EMatchEmpty _ ->
    (* TODO: not implemented *)
    Utils.report_error e "This language feature is not supported yet!"

and check_type env (e : Ast.expr) set tp =
  let cnt, _, tp' = infer_type env set e in
  (try unify tp tp' with
  | Cannot_unify ->
    let ctx = pp_context () in
    Utils.report_error e
      "This expression has type %s, but an expression was expected of type %s."
      (pp_type ctx 0 tp')
      (pp_type ctx 0 tp));
  cnt, e, tp'

let rec type_to_ftype (tp : Type.t) : SystemF.tp =
  match Type.view tp with
  | TUnit             -> SystemF.TUnit
  | TEmpty            -> SystemF.TEmpty
  | TBool             -> SystemF.TBool
  | TInt              -> SystemF.TInt
  | TUVar _           -> failwith "uvar in systemF"
  | TVar v            -> SystemF.TVar v
  | TArrow (t1, t2)   -> SystemF.TArrow (type_to_ftype t1, type_to_ftype t2)
  | TPair (t1, t2)    -> SystemF.TPair (type_to_ftype t1, type_to_ftype t2)
  | TCoPair (t1, t2)  -> SystemF.TCoPair (type_to_ftype t1, type_to_ftype t2)
  | TForallT (v, t2)  -> SystemF.TForallT (v, type_to_ftype t2)


let to_system_f (p : Ast.expr): SystemF.expr =
  let cnt, e, t = infer_type Env.empty Type.uvset_empty p in
  let cnt = cnt, e, generalize_type Type.uvset_empty t in
  let rec to_system_f (cnt, p, t : rec_t) = 
    match cnt, p.data, Type.view t with
    | _, EUnit, _          -> SystemF.EUnit
    | _, EBool v, _        -> SystemF.EBool v
    | _, ENum  v, _        -> SystemF.ENum v
    | _, EVar  v, _        -> SystemF.EVar v
    | One (cnt), EFn (v, e), Type.TArrow(t1, t2)        -> 
      SystemF.EFn (v, type_to_ftype t1, (to_system_f cnt))
    | One (cnt), EFix (f, x, e), Type.TArrow (t1, t2)    -> 
      let t1, t2 = type_to_ftype t1, type_to_ftype t2 in
      SystemF.EFix (f, x, SystemF.TArrow (t1, t2), t2, (to_system_f cnt))
    | Two(cnt1, cnt2), EApp (e1, e2), _     -> SystemF.EApp (to_system_f cnt1, to_system_f cnt2)
    | Two (cnt1, cnt2), ELet (x, e1, e2), _  -> SystemF.ELet (x, to_system_f cnt1, to_system_f cnt2)
    | Two (cnt1, cnt2), EPair _, _    -> SystemF.EPair (to_system_f cnt1, to_system_f cnt2)
    | One cnt, EFst _, _           -> SystemF.EFst (to_system_f cnt)
    | One cnt, ESnd _, _           -> SystemF.ESnd (to_system_f cnt)
    | One cnt, EInl _, Type.TCoPair (_, t2)           -> 
      SystemF.EInl ((to_system_f cnt), type_to_ftype t2)
    | One cnt, EInr _, Type.TCoPair (t1, _) ->
      SystemF.EInr (type_to_ftype t1, (to_system_f cnt))
    | Three(cnt, cnt1, cnt2), ECase (e, (c1_string, c1_expr), (c2_string, c2_expr)), _ -> 
      SystemF.ECase ((to_system_f cnt), 
                     (c1_string, (to_system_f cnt1)), 
                     (c2_string, (to_system_f cnt2)))
    | Three(cntb, cnt1, cnt2), EIf (b, e1, e2), _   ->
            SystemF.EIf ((to_system_f cntb), (to_system_f cnt1), (to_system_f cnt2))
    | Two(cnt1, cnt2), ESeq (e1, e2), _     ->
            SystemF.ESeq ((to_system_f cnt1), (to_system_f cnt2))
    | One cnt, EAbsurd e, _         -> 
      SystemF.EAbsurd ((to_system_f cnt), type_to_ftype t)
    | One cnt, ESelect (e, f), _    ->
      SystemF.ESelect((to_system_f cnt), f)
    | Three (cnt, cnt1, cnt2),
        EMatch  (e, name, (c1_string, c1_expr), (c2_string, c2_expr)),
        _  ->
      SystemF.EMatch ((to_system_f cnt), name,
                      (c1_string, (to_system_f cnt1)), 
                      (c2_string, (to_system_f cnt2)))
    | One cnt, EMatchEmpty e, _     -> 
      SystemF.EMatchEmpty ((to_system_f cnt), type_to_ftype t)
    | _, _, Type.TForallT (x, t') ->
      SystemF.ETFn (x, to_system_f )
    | _, _, _ -> failwith "internal error" in
  to_system_f cnt

let infer_type env set (e : Ast.expr) : Type.t =
    infer_type env set e |> third |> (fun x ->
    Printf.printf "%s" (string_of_type x);
    generalize_type Type.uvset_empty x)
