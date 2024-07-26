(* ============================================================================= *)

open Ast

let int2int_fun f =
  EExtern(fun lst ->
  match lst with
  | [VInt a; VInt b] ->
    begin try VInt (f a b) with
      | Division_by_zero -> raise (RuntimeError "Division by zero")
    end
  | _ -> failwith "internal error")

let int2bool_fun f =
  EExtern(fun lst ->
  match lst with
  | [VInt a; VInt b] -> VBool (f a b)
  | _ -> failwith "internal error")

let bool2bool_fun f =
  EExtern(fun a ->
  match a with
  | [VBool a; VBool b] -> VBool (f a b)
  | _ -> failwith "internal error")

let bool1bool_fun f =
  EExtern(fun a ->
  match a with
  | [VBool a] -> VBool (f a)
  | _ -> failwith "internal error")

let pair_fun f =
  EExtern(fun a ->
  match a with
  | [VPair(a,b)] -> f (a, b)
  | _ -> failwith "internal error")

let int1unit_fun f =
  EExtern(fun a ->
  match a with
  | [VInt n] ->
    begin try f n with
    | Invalid_argument _ ->
      raise (RuntimeError "Printing of non char")
    end; VUnit
  | _ -> failwith "internal error")

let printType str =
  let extern = EExtern(fun a ->
    match a with
    (* TODO check why is VUnit here *)
    | [VUnit] -> print_string str; VUnit
    | _ -> failwith "internal error")
  in
  EApp(extern, [EUnit])

let readInt =
  EExtern (fun a ->
  match a, read_int_opt () with
  | [VUnit], Some n -> VInt n
  | [VUnit], None -> raise (RuntimeError "Couldn't read int")
  | _, _ -> failwith "internal error")

let fail msg =
  EExtern(fun a ->
  match a with
  | [VUnit] -> raise (RuntimeError msg)
  | _ -> failwith "internal error")

module StringMap = Map.Make(String)

let builtins = [
  "add",  (int2int_fun ( + ), [2]);
  "sub",  (int2int_fun ( - ), [2]);
  "mult", (int2int_fun ( * ), [2]);
  "div",  (int2int_fun ( / ), [2]);
  "eq",   (int2bool_fun ( = ), [2]);
  "le",   (int2bool_fun ( <= ), [2]);
  "not",  (bool1bool_fun not, [1]);
  "fst",  (pair_fun fst, [1]);
  "snd",  (pair_fun snd, [1]);
  "readInt",    (readInt, [1]);
  "printInt",   (int1unit_fun print_int, [1]);
  "printAscii", (int1unit_fun (fun n -> Char.chr n |> print_char), [1]);
    (* printType requires special handling so it wont be here *)
] |> StringMap.of_list

let get_arity tp = 
    let open SystemF in
    let incr = function
      | [] -> failwith "internal error"
      | x :: xs -> (succ x) :: xs in
    let rec inner = function
      | TArrow(arr, _, tres) when Arrow.view_fold arr = FldUnfolded ->
        let xs = inner tres in
        1 :: xs
      | TArrow(_, _, tres) ->
        let xs = inner tres in
        incr xs
      | _ -> [0]
    in match inner tp with
      | 0 :: xs -> xs
      | xs -> xs

let fresh_var () = Core.Imast.IMAstVar.fresh ()

let string_of_int_list lst =
  List.map string_of_int lst |> String.concat ","

let lookup_builtin str tp_arity =
  let extern, arity =
  match StringMap.find_opt str builtins with
  | None -> failwith ("Internal error: unbound variable \""^str^"\"")
  | Some res -> res
  in
  if List.equal (=) tp_arity arity then extern else
  match tp_arity, arity with
  | [1;1], [2] ->
    let x = fresh_var () in
    let y = fresh_var () in
    EFn([x], EFn([y], EApp(extern, [EVar x; EVar y])))
  | [1;0], [1]
  | [2;0], [2] -> extern
  | _ -> failwith (
    Printf.sprintf "internal error: builtin coerssion. expected [%s], actual [%s]"
    (string_of_int_list arity) (string_of_int_list tp_arity))
