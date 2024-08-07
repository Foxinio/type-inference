open Utils
open Main
module Effect = Core.Effect

let refresh_ctors = EnsureWellTyped.check_ctors

(* ========================================================================= *)
(* Analysis *)

let extend_var env xs tp =
  let rec inner env xs tp arr =
    match xs, tp with
    | x :: xs, TArrow(arr, tp1, tp2) ->
      inner (Env.add_var env x tp1) xs tp2 arr
    | [], tp -> tp, env, arr
    | _ :: _, _ -> Utils.report_too_many_arguments ()
  in
  match xs, tp with
  | x :: xs, TArrow(arr, tp1, tp2) ->
    inner (Env.add_var env x tp1) xs tp2 arr
  | _ -> Utils.report_too_many_arguments ()

let unfold_opt = function
  | None -> ()
  | Some arr ->
    Arrow.set_unfolded arr

let refresh_tvars env tp =
  let rec inner arr_opt = function
    | TUnit | TInt | TBool | TEmpty | TVar _ ->
      unfold_opt arr_opt
    | TForallT (_, tp) ->
      unfold_opt arr_opt;
      inner None tp
    | TArrow(arr, targ, tres) ->
      inner None targ;
      inner (Some arr) tres
    | TADT (_, tps) ->
      unfold_opt arr_opt;
      List.iter (inner None) tps
    | TPair (tp1, tp2) ->
      unfold_opt arr_opt;
      inner None tp1;
      inner None tp2
  in
  inner None tp;
  EnsureWellTyped.check_well_scoped env tp

let rec fill_unfolds env e =
  let open Effect in
  match e with
  | EUnit   -> TUnit
  | EBool _ -> TBool
  | ENum _  -> TInt
  | EVar x  -> Env.lookup_var env x

  | EFn (args, body, tp) ->
    let tp' = refresh_tvars env tp in
    let tres, env, arr = extend_var env args tp' in
    Arrow.set_unfolded arr;
    fill_no_ret env body;
    tp'

  | EFix (f, args, body, tp) ->
    let tp' = refresh_tvars env tp in
    let env = Env.add_var env f tp' in
    let tres, env, arr = extend_var env args tp' in
    Arrow.set_unfolded arr;
    fill_no_ret env body;
    tp'

  | EApp (e1, es) ->
    let tp1 = fill_unfolds env e1 in
    fill_unfolds_in_app env es tp1

  | ETFn(a, body) ->
    let env, b = Env.extend_tvar env a in
    let tp = fill_unfolds env body in
    TForallT(b, tp)

  | ETApp(e, tps) ->
    begin match fill_unfolds env e with
    | TForallT(args, body) when List.length args = List.length tps ->
      let tps = List.map (refresh_tvars env) tps in
      Subst.subst_list body args tps
    | tp -> Utils.report_unexpected_type tp "TForallT"
    end

  | ELet(x, e1, e2) ->
    let tp1 = fill_unfolds env e1 in
    let env = Env.add_var env x tp1 in
    let tp2 = fill_unfolds env e2 in
    tp2

  | EExtern(name, tp) ->
    refresh_tvars env tp

  | EPair(e1, e2) ->
    let tp1 = fill_unfolds env e1 in
    let tp2 = fill_unfolds env e2 in
    TPair(tp1, tp2)

  | EFst e ->
    begin match fill_unfolds env e with
    | TPair (tp1, _) -> tp1
    | actual -> Utils.report_unexpected_type actual "TPair"
    end

  | ESnd e ->
    begin match fill_unfolds env e with
    | TPair(_, tp2) -> tp2
    | actual -> Utils.report_unexpected_type actual "TPair"
    end

  | EIf(e1, e2, e3) ->
    fill_no_ret env e1;
    let tp2 = fill_unfolds env e2 in
    fill_no_ret env e3;
    tp2

  | ESeq(e1, e2) ->
    fill_no_ret env e1;
    let tp = fill_unfolds env e2 in
    tp

  | EType(alias, tvars, ctor_defs, body) ->
    let env, tvars = Env.extend_tvar env tvars in
    let ctor_defs' = refresh_ctors env ctor_defs in
    let env = Env.extend_ctors env ctor_defs' alias tvars in
    fill_unfolds env body

  | ECtor (name, adt_args, body) ->
    let expected, alias, tvars = Env.lookup_ctor env name in
    let adt_args' = List.map (refresh_tvars env) adt_args in
    fill_no_ret env body;
    TADT (alias, adt_args')

  | EMatch(body, defs, tp) ->
    let tp' = refresh_tvars env tp in
    begin match fill_unfolds env body with
    | TADT(alias, args) ->
      let f (ctor, x, e) =
        let env, _ = Env.extend_clause env x ctor args in
        fill_no_ret env e
      in
      List.iter f defs;
      tp'
    | TEmpty ->
      tp'
    | actual -> Utils.report_unexpected_type actual "TADT or TEmpty"
    end

and fill_no_ret env e =
  let _ = fill_unfolds env e in
  ()

and fill_unfolds_in_app env args tp =
  let rec inner args tp arr =
    match args, tp with
    | [], tres -> arr, tres
    | e :: args, TArrow(arr, _, tres) ->
      fill_no_ret env e;
      inner args tres arr
    | _ :: _, _ ->
      Utils.report_too_many_arguments ()
  in
  match args, tp with
  | e :: args, TArrow(arr, _, tres) ->
      fill_no_ret env e;
    let arr, tp = inner args tres arr in
    Arrow.set_unfolded arr;
    tp
  |  _ ->
      Utils.report_too_many_arguments ()

(* ========================================================================= *)
(* Crude analysis *)

let rec unfold_type = function
  | TUnit | TEmpty | TBool | TInt | TVar _ -> ()
  | TForallT (_, tp) ->
    unfold_type tp
  | TPair(tp1, tp2) ->
    unfold_type tp1;
    unfold_type tp2
  | TADT (_, args) ->
    List.iter unfold_type args
  | TArrow (arr, tp1, tp2) ->
    Arrow.set_unfolded arr;
    unfold_type tp1;
    unfold_type tp2

let rec unfold_expr = function
  | EUnit | EBool _ | ENum _ | EVar _ -> ()
  | EFn (_, body, tp) ->
    unfold_type tp;
    unfold_expr body
  | EFix (_, _, body, tp) ->
    unfold_type tp;
    unfold_expr body
  | EApp(e1, es) ->
    unfold_expr e1;
    List.iter unfold_expr es
  | ETFn (_, body) ->
    unfold_expr body
  | ETApp(e, _) ->
    unfold_expr e
  | ELet(x, e1, e2) ->
    unfold_expr e1;
    unfold_expr e2
  | EExtern (_, tp) ->
    unfold_type tp
  | EPair(e1, e2) ->
    unfold_expr e1;
    unfold_expr e2
  | EFst e ->
    unfold_expr e
  | ESnd e ->
    unfold_expr e
  | EIf(e1, e2, e3) -> 
    unfold_expr e1;
    unfold_expr e2;
    unfold_expr e3
  | ESeq(e1, e2) -> 
    unfold_expr e1;
    unfold_expr e2
  | EType (_, _, ctors, body) ->
    List.iter unfold_ctors ctors;
    unfold_expr body
  | ECtor (_, tps, body) ->
    List.iter unfold_type tps;
    unfold_expr body
  | EMatch(e, clauses, tp) ->
    unfold_expr e;
    List.iter unfold_clause clauses;
    unfold_type tp

and unfold_ctors = function
  | (_, tp) ->
    unfold_type tp

and unfold_clause = function
  | (_, _, e) ->
    unfold_expr e


(* ========================================================================= *)
(* Transformation *)

let refresh_tvars = EnsureWellTyped.check_well_scoped

let fresh_var () =
  let name = Core.Imast.VarTbl.gen_name () in
  let x = Core.Imast.VarTbl.fresh_var name in
  x

let minor_append x xs =
  match xs with
  | [] -> [[x]]
  | [] :: xss -> [x] :: xss
  | xs :: xss -> (x :: xs) :: xss

let rec split_arrow body xs tp =
  let rec inner acc xs tp =
    match xs, tp with
    | x :: xs, TArrow(arr, _, tp2) when Arrow.view_fold arr = FldFolded ->
      inner (x :: acc) xs tp2
    | [], _ -> List.rev acc, body
    | [x], _ ->
      List.rev (x :: acc), body
    | x :: xs, TArrow(_, _, tp) ->
      let xs, body = split_arrow body xs tp in
      let body' = EFn (xs, body, tp) in
      List.rev (x :: acc), body'
    | _ :: _, _ -> raise (Invalid_argument "split_arrow expects an arrow")
  in inner [] xs tp

let destruct_tarrow = function
  | TArrow(arr, targ, tres) -> arr, targ, tres
  | tp -> Utils.report_unexpected_type tp "TArrow"

let make_wrapper e' (eff : Effect.t) =
  match eff with
  | EffPure -> Fun.id, e'
  | EffImpure ->
    let x' = fresh_var () in
    (fun e2 -> ELet(x', e', e2)), EVar x'

let rec unfold_app e' = function
  | [] -> e'
  | x :: xs -> unfold_app (EApp(e', List.rev x)) xs

let rec is_coerse_id tp_expected tp_given =
  match tp_expected, tp_given with
  | TArrow(arr1, _, _), TArrow(arr2, _, _) 
      when Arrow.view_fold arr1 = FldUnfolded
      && Arrow.view_fold arr2 = FldUnfolded ->
    true
  | TArrow(arr1, _, tres1), TArrow(arr2, _, tres2) ->
    Arrow.view_fold arr1 = Arrow.view_fold arr2
    && is_coerse_id tres1 tres2
  | TPair(tp1a, tp2a), TPair(tp1b, tp2b) ->
    is_coerse_id tp1a tp1b && is_coerse_id tp2a tp2b
  | TForallT(_, _), _
  | _, TForallT(_, _) ->
    Core.Utils.report_internal_error "is_coerse_id error: TForallT is not expected at this point"
  | _ -> true

let rec transform_expr env e : expr * tp * Effect.t =
  match e with
  | EUnit -> e, TUnit, EffPure
  | EBool _ -> e, TBool, EffPure
  | ENum _ -> e, TInt, EffPure
  | EVar x -> EVar x, Env.lookup_var env x, EffPure

  | EFn (xs, body, tp) ->
    let tp' = refresh_tvars env tp in
    let _, env, _ = Env.extend_var env xs tp' in
    let body', _, _  = transform_expr env body in
    let xs, body' = split_arrow body' xs tp' in
    EFn (xs, body', tp'), tp', EffPure

  | EFix (f, xs, body, tp) ->
    let tp' = refresh_tvars env tp in
    let _, env, _ = Env.extend_var env xs tp' in
    let body', _, _ = transform_expr (Env.add_var env f tp') body in
    let xs, body' = split_arrow body' xs tp' in
    EFix (f, xs, body', tp'), tp', EffPure

  | EApp (e1, es) ->
    let e1', tp, eff = transform_expr env e1 in
    transform_app env e1' es tp eff

  | EExtern (name, tp) ->
    let tp' = refresh_tvars env tp in
    EExtern (name, tp'), tp', EffPure

  | ETFn (a, body) ->
    let env, b = Env.extend_tvar env a in
    let body', tp, eff = transform_expr env body in
    ETFn (b, body'), TForallT(b, tp), eff

  | ETApp (e, tps) ->
    begin match transform_expr env e with
    | e', TForallT(args, body), eff ->
      let tps = List.map (refresh_tvars env) tps in
      ETApp (e', tps),
      Subst.subst_list body args tps,
      eff
    | _, actual, _ -> Utils.report_unexpected_type actual "TForallT"
    end

  | ELet (x, e1, e2) ->
    let e1', tp1, eff1 = transform_expr env e1 in
    let env = Env.add_var env x tp1 in
    let e2', tp2, eff2 = transform_expr env e2 in
    ELet (x, e1', e2'), tp2, Effect.join eff1 eff2

  | EPair (e1, e2) ->
    let e1', tp1, eff1 = transform_expr env e1 in
    let e2', tp2, eff2 = transform_expr env e2 in
    EPair (e1', e2'), TPair (tp1, tp2), Effect.join eff1 eff2

  | EFst e ->
    begin match transform_expr env e with
    | e', TPair (tp1, _), eff ->
      EFst e', tp1, eff
    | _, actual, _ -> Utils.report_unexpected_type actual "TPair"
    end

  | ESnd e ->
    begin match transform_expr env e with
    | e', TPair (_, tp2), eff ->
      ESnd e', tp2, eff
    | _, actual, _ -> Utils.report_unexpected_type actual "TPair"
    end

  | EIf (e1, e2, e3) ->
    let e1', _, eff1 = transform_expr env e1 in
    let e2', tp, eff2 = transform_expr env e2 in
    let e3', _, eff3 = transform_expr env e3 in
    EIf (e1', e2', e3'), tp, Effect.join eff1 (Effect.join eff2 eff3)

  | ESeq (e1, e2) ->
    let e1', _, eff1 = transform_expr env e1 in
    let e2', tp2, eff2 = transform_expr env e2 in
    ESeq (e1', e2'), tp2, Effect.join eff1 eff2

  | EType (alias, tvars, ctor_defs, body) ->
    let env, tvars = Env.extend_tvar env tvars in
    let ctor_defs' = refresh_ctors env ctor_defs in
    let env = Env.extend_ctors env ctor_defs' alias tvars in
    let body', tp, eff = transform_expr env body in
    EType (alias, tvars, ctor_defs', body'), tp, eff

  | ECtor (name, adt_args, body) ->
    let _, alias, _ = Env.lookup_ctor env name in
    let adt_args' = List.map (refresh_tvars env) adt_args in
    let body', _, eff = transform_expr env body in
    ECtor (name, adt_args', body'),
    TADT (alias, adt_args'), eff

  | EMatch (body, clauses, tp) ->
    let tp = refresh_tvars env tp in
    let body', body_tp, eff = transform_expr env body in
    let clauses', eff' = match body_tp with
      | TADT(alias, args) ->
        let f (ctor, x, e) =
          let env, _ = Env.extend_clause env x ctor args in
          let e', tp, _ = transform_expr env e in
          (ctor, x, e')
        in
        List.map f clauses, Effect.EffImpure
      | TEmpty -> [], Effect.EffPure
      | actual -> Utils.report_unexpected_type actual "TADT or TEmpty"
    in
    EMatch (body', clauses', tp), tp, Effect.join eff eff'

(** Setup application to match conditions presented in EnsureWellTyped

   Takes in environment,
    transformed expression e1' (with type and effect)
    list of transformed expressions es' (with effect)
  *)
and transform_app env e1' es tp eff =
  let counter = ref 0 in
  let curring es tp eff =
    let rec generate_args args xs = function
      | TArrow(arr, _, tres) when Arrow.view_fold arr = FldFolded ->
        let x = fresh_var () in
        generate_args (EVar x :: args) (x :: xs) tres
      | tp ->
        let rec generate_lets lets args' eff = function
          | (e, eff') :: rest when eff' = Effect.EffImpure ->
            let x = fresh_var () in
            generate_lets ((x, e) ::lets) (EVar x::args')
              (Effect.join eff eff') rest
          | (e, _) :: rest ->
            generate_lets lets (e::args') eff rest
            (* lets are in reverse order,
                but instead of List.rev we will fold_left *)
          | [] ->
            lets, List.rev_append args' args, xs, eff
        in generate_lets [] [] eff es
    in generate_args [] [] tp
  in
  let rec uncurring acc es tp =
    match es, tp with

    | [e], TArrow(arr, targ, tres) when Arrow.view_fold arr = FldUnfolded ->
      let e', eff' = coerse_argument env e targ in
      let eff'', args = List.fold_left
        (fun (eff, acc) (e, eff') -> Effect.join eff eff', e :: acc)
        (eff,[])
        ((e', eff') :: acc) in
      incr counter;
      EApp(e1', args), tres, eff''


    | [e], TArrow(arr, targ, tres) ->
      let e', eff' = coerse_argument env e targ in
      let e1wrapper, e1'' = make_wrapper e1' eff in
      incr counter;
      let lets, args, xs, eff'' = curring ((e', eff') :: acc) tp eff in
      let curried = EFn(xs, EApp(e1'', args), tres) in
      let lets = List.fold_left
          (fun e (x, e1) -> ELet(x, e1, e)) curried lets in
      e1wrapper lets, tres, eff''

    | e :: es, TArrow(arr, targ, tres) when Arrow.view_fold arr = FldFolded ->
      let e', eff' = coerse_argument env e targ in
      incr counter;
      uncurring ((e',eff') :: acc) es tres

    | e :: es, TArrow(arr, targ, tres) when Arrow.view_fold arr = FldUnfolded ->
      let e', eff' = coerse_argument env e targ in
      let eff'', args = List.fold_left
        (fun (eff, acc) (e, eff') -> Effect.join eff eff', e :: acc)
        (eff,[])
        ((e', eff') :: acc) in
      incr counter;
      transform_app env (EApp (e1', args)) es tp eff'


    | es, tp ->
      let eff', acc = List.fold_left
        (fun (eff, acc) (e, eff') -> Effect.join eff eff', e :: acc)
        (eff,[])
        acc in
      incr counter;
      transform_app env (EApp (e1', acc)) es tp eff'

  in uncurring [] es tp

and coerse_argument env e expected =
  let e', actual, eff = transform_expr env e in
  if is_coerse_id actual expected then e', eff else
  let ewrapper, e' =
    match eff, expected with
    | _, TPair _ -> Fun.id, e'
    | EffImpure, _ ->
      let x' = fresh_var () in
      (fun e2 -> ELet(x', e', e2)), EVar x'
    | _ -> Fun.id, e'
  in
  let res = add_coersion env e' expected actual |> ewrapper, eff in
  res

and maybe_add_coersion env e' expected actual =
  if is_coerse_id actual expected then e' else
  add_coersion env e' expected actual

and add_coersion env e' expected actual =
  match expected, actual with
  | TPair (t1, t2), TPair(t1', t2') ->
    let x = fresh_var () in
    let e1 = maybe_add_coersion env (EFst (EVar x)) t1 t1' in
    let e2 = maybe_add_coersion env (ESnd (EVar x)) t2 t2' in
    ELet(x, e', EPair(e1, e2))

  | TArrow _, TArrow _ ->
    let rec inner1 e' tret =
      let rec inner2 xs eff vars actual expected =
        let arr1, _, actual   = destruct_tarrow actual in
        let arr2, _, expected = destruct_tarrow expected in
        match Arrow.view_fold arr1, Arrow.view_fold arr2 with

        (* e: (_, ...->)-> *)
        (* e': _, ...->    *)
        | FldFolded, FldFolded ->
          let x = fresh_var () in
          let eff' = Effect.join eff @@ Arrow.view_eff arr1 in
          inner2 (x :: xs) eff' (minor_append (EVar x) vars) actual expected

        (* e: (_, ...->)-> *)
        (* e': _->...->    *)
        | FldUnfolded, FldFolded ->
          let x = fresh_var () in
          let eff' = Effect.join eff @@ Arrow.view_eff arr1 in
          inner2 (x :: xs) eff' ([] :: minor_append (EVar x) vars) actual expected

        (* e: (_->...->)-> *)
        (* e': _, ...->    *)
        | FldFolded, FldUnfolded ->
          let x = fresh_var () in
          let eff' = Effect.join eff @@ Arrow.view_eff arr1 in
          let xs, vars = x :: xs, minor_append (EVar x) vars in
          if eff' = EffPure then
            let body = inner1 e' expected vars actual expected in
            EFn(List.rev xs, body, tret)
          else
            let x' = fresh_var () in
            let body =
              inner1 (EVar x') expected [List.hd vars] actual expected in
            let body' =
              ELet(x', unfold_app e' (List.rev @@ List.tl vars), body) in
            EFn(List.rev xs, body', tret)

        (* e: (_->...->)-> *)
        (* e': _->...->    *)
        | FldUnfolded, FldUnfolded ->
          let x = fresh_var () in
          let _ = Effect.join eff @@ Arrow.view_eff arr1 in
          let xs, vars = x :: xs, minor_append (EVar x) vars in
          EFn(List.rev xs, unfold_app e' (List.rev vars), tret)

      in inner2 [] EffPure
    in
    inner1 e' expected [] actual expected
  | _ -> e'


let transform_with_folding p =
  ignore @@ fill_unfolds Env.empty p;
  Core.Utils.dump_ast (PrettyPrinter.pp_expr Utils2.Env.empty p);
  let p, _, _ = transform_expr Env.empty p in
  p

let crude_transform_with_folding p =
  unfold_expr p;
  let p, _, _ = transform_expr Env.empty p in
  p

(* ######################################################################### *)
(* TESTS *)

let%test_module "SystemF.FillFolding Testing module" =
  (module struct
    module VarTbl = Core.Imast.VarTbl
    open PrettyPrinter

  let _ =
    LmConfig.verbose_internal_errors := true;
    LmConfig.print_asts := true

  let eq_mod_vars e1 e2 =
    let rec inner e1 e2 =
        match e1, e2 with
        | EExtern (_, _), EExtern (_, _) | EUnit, EUnit
        | EBool _, EBool _ | ENum _, ENum _ | EVar _, EVar _ -> true
        | EFn (xs1, e1, _), EFn (xs2, e2, _) ->
          List.length xs1 = List.length xs2
          && inner e1 e2
        | EFix (_,xs1,body1,_), EFix (_,xs2,body2,_) ->
          List.length xs1 = List.length xs2
          && inner body1 body2
        | EApp (e1, es1), EApp (e2, es2) ->
          inner e1 e2
          && List.length es1 = List.length es2
          && List.for_all2 inner es1 es2
        | ETFn (_, body1), ETFn (_, body2) ->
          inner body1 body2
        | ETApp (e1, _), EApp (e2, _) ->
          inner e1 e2
        | ELet (_, e1, e2), ELet (_, e3, e4) ->
          inner e1 e3 && inner e2 e4
        | EPair (e1, e2), EPair (e3, e4) ->
          inner e1 e3 && inner e2 e4
        | EFst e1, EFst e2 ->
          inner e1 e2
        | ESnd e1, ESnd e2 ->
          inner e1 e2

      (* not perfect, but will do *)
      | _ -> false
  in inner e1 e2

  let arr() = Arrow.fresh()
  let unf_arr () =
    let arr = Arrow.fresh() in
    Arrow.set_unfolded arr;
    arr
  let imp_arr () =
    let arr = Arrow.fresh() in
    Arrow.set_impure arr;
    arr

  let bad_arr () =
    let arr = Arrow.fresh() in
    Arrow.set_unfolded arr;
    Arrow.set_impure arr;
    arr

  let gen_var () = VarTbl.fresh_var (VarTbl.gen_name())

  let gen_vars n =
    Seq.forever gen_var |> Seq.take n |> List.of_seq

  let gen_env tp =
    let x = gen_var () in
    x, Env.add_var Env.empty x tp

  let e_fn n e = EFn(gen_vars n, e, TBool)
  let e_var x = EVar x

  let reshufle xss arity =
    let rec inner acc = function
      | [[]], [0] -> [List.rev acc]
      | xss, 0 :: arity ->
        List.rev acc :: inner [] (xss,arity)
      | [] :: xss, arity ->
        inner acc (xss,arity)
      | (x::xs)::xss, n :: arity ->
        inner (x::acc) (xs::xss,n-1::arity)
      | [],_::_
      | (_::_)::_,[]
      | [], [] -> failwith "reshufle"
    in inner [] (xss,arity)

  let pp_list pp xs =
    List.map pp xs
    |> String.concat ", "
    |> Printf.sprintf "[%s]"

  let%test "reshufle1" =
    let xss = [[1]; [2;3]] in
    let arity = [1;2] in
    let xss' = reshufle xss arity in
    xss' = xss

  let%test "reshufle2" =
    let xss = [[1]; [2;3]] in
    let arity = [2;1] in
    let xss' = reshufle xss arity in
    let xss'' = [[1;2]; [3]] in
    xss' = xss''

  let%test "reshufle3" =
    let xss = [[1;2;3];[4;5;6]] in
    let arity = [2;2;2] in
    let xss' = reshufle xss arity in
    let xss'' = [[1;2];[3;4];[5;6]] in
    xss' = xss''

  let%test "reshufle4" =
    let xss = [[1];[2;3];[4;5;6]] in
    let arity = [2;2;2] in
    let xss' = reshufle xss arity in
    let xss'' = [[1;2];[3;4];[5;6]] in
    xss' = xss''

  let rec build_arrow = function
    | [] -> TUnit
    | 0 :: _ -> failwith "building"
    | 1 :: lst -> TArrow(unf_arr(), TUnit, build_arrow lst)
    | n :: lst -> TArrow(arr(), TUnit, build_arrow (n-1::lst))

  let rec build_corr_fn = function
    | [] -> [], Fun.id
    | n :: lst ->
      let xs = gen_vars n in
      let tp = build_arrow (n::lst) in
      let args, fn = build_corr_fn lst in
      xs::args, fun e -> EFn(xs, fn e, tp)
  and build_app e = function
    | [] -> e
    | xs :: xss ->
      let xs' = List.map e_var xs in
      build_app (EApp(e, xs')) xss

  and build_fn e = function
    | [] -> e
    | n :: lst ->
      let tp = build_arrow (n::lst) in
      EFn(gen_vars n, build_fn e lst, tp)

  let build_coerse e given accepted =
    let args, builder = build_corr_fn accepted in
    let args' = reshufle args given in
    let e = build_app e args' in
    builder e

  let rec impure_arrow n tp =
    match n, tp with
    | 0, TArrow(arr,_,_) -> Arrow.set_impure arr
    | n, _ when n < 0 -> failwith "error"
    | n, TArrow(_,_,tres) -> impure_arrow (n-1) tres
    | _ -> failwith "error"

  let dump_expr env e =
    let str = PrettyPrinter.pp_expr (Env.to_env2 env) e in
    Printf.eprintf "%s\n%!" str

  let dump_type tp =
    let str = PrettyPrinter.pp_type tp in
    Printf.eprintf "%s\n%!" str

  let print env e tp e' e_corr =
    if false then (
      prerr_endline @@ String.make 80 '#';
      prerr_endline "dump coersed e";
      dump_expr env e;
      prerr_newline ();
      prerr_endline "expected tp";
      dump_type tp;
      prerr_newline ();
      prerr_endline "dump resulting e'";
      dump_expr env e';
      prerr_newline ();
      prerr_endline "dump expected e_corr";
      dump_expr env e_corr;
      prerr_newline ())

  let check_type env e tp =
    let tp',_ = EnsureWellTyped.infer_type env e in
    EnsureWellTyped.assert_type_eq env e tp tp'

  let infer_type env e =
    let tp, _ = Utils2.infer_type (Env.to_env2 env) e in
    tp

  let%test "coerse_argument test: simple id" =
    let tp = TBool in
    let e  = EBool true in
    let e', eff = coerse_argument Env.empty e tp in
    assert(e=e');
    assert(eff=EffPure);
    true

  let%test "coerse_argument test: complex id" =
    let tp = build_arrow [2;1] in
    let x, env = gen_env TUnit in
    let e = build_fn (EVar x) [2;1] in
    let e', eff = coerse_argument env e tp in
    assert(e=e');
    assert(eff=EffPure);
    true

  let%test "coerse_argument test: pair id" =
    let tp_inner = build_arrow [2;1] in
    let tp = TPair(tp_inner, TUnit) in
    let x, env = gen_env TUnit in
    let e_inner = build_fn (EVar x) [2;1] in
    let e = EPair(e_inner, EUnit) in
    let e', eff = coerse_argument env e tp in
    assert(e=e');
    assert(eff=EffPure);
    true

  let%test "coerse_argument test: split 2->1,1" =
    let tp_expected = build_arrow [1;1] in
    let tp_actual = build_arrow [2] in
    let x, env = gen_env tp_actual in
    let e = build_fn EUnit [2] in
    let e_corr = build_coerse (EVar x) [2] [1;1] in
    check_type env e tp_actual;
    let e', eff = coerse_argument env (EVar x) tp_expected in
    check_type env e' tp_expected;
    assert(eq_mod_vars e' e_corr);
    assert(eff=EffPure);
    true

  let%test "coerse_argument test: merge 1,1->2" =
    let tp_actual = build_arrow [1;1] in
    let tp_expected = build_arrow [2] in
    let x, env = gen_env tp_actual in
    let e = build_fn EUnit [1;1] in
    let e_corr = build_coerse (EVar x) [1;1] [2] in
    check_type env e tp_actual;
    let e', eff = coerse_argument env (EVar x) tp_expected in
    check_type env e' tp_expected;
    print env e tp_expected e' e_corr;
    assert(eq_mod_vars e' e_corr);
    assert(eff=EffPure);
    true

  let%test "coerse_argument test: 1,2->2,1" =
    let tp_expected = build_arrow [2;1] in
    let tp_actual   = build_arrow [1;2] in
    let x, env = gen_env tp_actual in
    let e = build_fn EUnit [1;2] in
    check_type env e tp_actual;
    let e', _ = coerse_argument env (EVar x) tp_expected in
    check_type env e' tp_expected;
    let e_corr = build_coerse (EVar x) [1;2] [2;1] in
    print env e tp_expected e' e_corr;
    assert(eq_mod_vars e' e_corr);
    true

  let%test "coerse_argument test: 2,1->1,2" =
    let tp_expected = build_arrow [1;2] in
    let tp_actual   = build_arrow [2;1] in
    let x, env = gen_env tp_actual in
    let e = build_fn EUnit [2;1] in
    check_type env e tp_actual;
    let e', _ = coerse_argument env (EVar x) tp_expected in
    check_type env e' tp_expected;
    let e_corr = build_coerse (EVar x) [2;1] [1;2] in
    print env e tp_expected e' e_corr;
    assert(eq_mod_vars e' e_corr);
    true

  let%test "coerse_argument test: 1,2,2->2,2,1" =
    let tp_expected = build_arrow [2;2;1] in
    let tp_actual   = build_arrow [1;2;2] in
    let x, env = gen_env tp_actual in
    let e = build_fn EUnit [1;2;2] in
    check_type env e tp_actual;
    let e', _ = coerse_argument env (EVar x) tp_expected in
    check_type env e' tp_expected;
    let e_corr = build_coerse (EVar x) [1;2;2] [2;2;1] in
    print env e tp_expected e' e_corr;
    assert(eq_mod_vars e' e_corr);
    true

  let%test "coerse_argument test: 1,2,3->2,2,2" =
    let tp_expected = build_arrow [2;2;2] in
    let tp_actual   = build_arrow [1;2;3] in
    let x, env = gen_env tp_actual in
    let e = build_fn EUnit [1;2;3] in
    check_type env e tp_actual;
    let e', _ = coerse_argument env (EVar x) tp_expected in
    check_type env e' tp_expected;
    let e_corr = build_coerse (EVar x) [1;2;3] [2;2;2] in
    print env e tp_expected e' e_corr;
    assert(eq_mod_vars e' e_corr);
    true

  let%test "coerse_argument test: 2,2,1->1,2,2" =
    let tp_expected = build_arrow [1;2;2] in
    let tp_actual   = build_arrow [2;2;1] in
    let x, env = gen_env tp_actual in
    let e = build_fn EUnit [2;2;1] in
    check_type env e tp_actual;
    let e', _ = coerse_argument env (EVar x) tp_expected in
    check_type env e' tp_expected;
    let e_corr = build_coerse (EVar x) [2;2;1] [1;2;2] in
    print env e tp_expected e' e_corr;
    assert(eq_mod_vars e' e_corr);
    true

  let%test "coerse_argument test: coerse pair" =
    let tp_expected = TPair(build_arrow [2;2],   TUnit) in
    let tp_actual   = TPair(build_arrow [1;2;1], TUnit) in
    let x, env = gen_env tp_actual in
    let e = EPair(build_fn EUnit [1;2;1], EUnit) in
    check_type env e tp_actual;
    let e', _ = coerse_argument env e tp_expected in
    check_type env e' tp_expected;
    let e_corr_fst = build_coerse (EFst (EVar x)) [1;2;1] [2;2] in
    let e_corr_snd = ESnd (EVar x) in
    let e_corr = ELet(x, e, EPair(e_corr_fst, e_corr_snd)) in
    print env e tp_expected e' e_corr;
    assert(eq_mod_vars e' e_corr);
    true

  let%test "check_type test: does it find negatives" =
    let wrong_tp = build_arrow [2;1] in
    let x, env = gen_env TUnit in
    let e = build_fn (EVar x) [1;2] in
    let correct_tp = infer_type env e in
    not @@ Order.type_equal wrong_tp correct_tp

end)
