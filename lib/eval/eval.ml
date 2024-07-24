(** The evaluator *)

open Erase

module Env : sig
  type t

  val empty : t

  val add : t -> var -> value -> t
  val extend : t -> var list -> value list -> t

  val lookup : t -> var -> value

  val with_name_map : string Core.Imast.VarTbl.t -> t

  val capture : t -> value Core.Imast.VarMap.t
end = struct
  open Core.Imast

  type t = {
    vmap : value VarMap.t;
    name_map : string VarTbl.t;
  }

  let empty = {
    vmap = VarMap.empty;
    name_map = VarTbl.create 11;
  }

  let with_name_map tbl =
    { empty with name_map = tbl }

  let add env x v =
    { env with vmap=VarMap.add x v env.vmap }

  let extend env xs vs =
    let f env x v = VarMap.add x v env in
    try
      { env with vmap=List.fold_left2 f env.vmap xs vs }
    with
      | Invalid_argument _ ->
        Core.Utils.report_runtime_error "coerssion done incorrectly,
      function requires different amount of arguments than reveived"


  let lookup_name {name_map;_} x =
    VarTbl.find name_map x

  let lookup env x =
    match VarMap.find_opt x env.vmap with
    | None   -> failwith ("runtime error: unbound variable "
      ^ lookup_name env x)
    | Some v -> v

  let capture env = env.vmap
end

let clo_counter = ref 0

let v_clo f =
  incr clo_counter;
  VClo f

let rec eval env (e : Erase.expr) =
  match e with
  | EUnit   -> VUnit
  | EBool b -> VBool b
  | ENum  n -> VInt  n
  | EVar  x -> Env.lookup env x
  | EFn(xs, body) ->
    v_clo (fun vs ->
      eval (Env.extend env xs vs) body)
  | EFix(f, xs, e) ->
    let rec func v =
      eval (Env.extend (Env.add env f (Lazy.force_val f_clo)) xs v) e
    and f_clo = lazy (v_clo func) in
    Lazy.force_val f_clo
  | EExtern f ->
    v_clo f
  | EApp(e1, es) ->
    begin match eval env e1 with
    | VClo f ->
      let vs = List.map (eval env) es in
      f vs
    | _ -> failwith "internal type error"
    end
  | ELet(x, e1, e2) ->
    eval (Env.add env x (eval env e1)) e2
  | EPair(e1, e2) ->
    VPair (eval env e1, eval env e2)
  | EIf(e1, e2, e3) ->
    begin match eval env e1 with
    | VBool true  -> eval env e2
    | VBool false -> eval env e3
    | _ -> failwith "internal type error"
    end
  | ESeq(e1, e2) ->
    begin match eval env e1 with
    | VUnit -> eval env e2
    | _ -> failwith "internal type error"
    end
  | ECtor(name, body) ->
    VADT(name, eval env body)
  | EMatch(e, clauses) ->
    begin match eval env e with
    | VADT(n, v) ->
      let x, expr = clauses.(n) in
      eval (Env.add env x v) expr
    | _ -> failwith "internal type error"
    end

let rec pp_value v =
  match v with
  | VUnit   -> "()"
  | VBool b -> string_of_bool b
  | VInt  n -> string_of_int  n
  | VClo  _ -> "<fn>"
  | VPair(v1, v2) -> Printf.sprintf "(%s, %s)" (pp_value v1) (pp_value v2)
  | VADT _ -> "<abstr>"


let eval_program (p, env) =
  let env = Env.with_name_map env in
  eval env p |> pp_value |> print_endline
