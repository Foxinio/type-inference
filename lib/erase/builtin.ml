(* ============================================================================= *)

open Ast

let int2int_fun f =
  EExtern(fun a ->
  VClo(fun b ->
  match a, b with
  | VInt a, VInt b ->
    begin try VInt (f a b) with
    | Division_by_zero -> raise (RuntimeError "Division by zero")
    end
  | _ -> failwith "internal error"))

let int2bool_fun f =
  EExtern(fun a ->
  VClo(fun b ->
  match a, b with
  | VInt a, VInt b -> VBool (f a b)
  | _ -> failwith "internal error"))

let bool2bool_fun f =
  EExtern(fun a ->
  VClo(fun b ->
  match a, b with
  | VBool a, VBool b -> VBool (f a b)
  | _ -> failwith "internal error"))

let bool1bool_fun f =
  EExtern(fun a ->
  match a with
  | VBool a -> VBool (f a)
  | _ -> failwith "internal error")

let pair_fun f =
  EExtern(fun a ->
  match a with
  | VPair(a,b) -> f (a, b)
  | _ -> failwith "internal error")

let int1unit_fun f =
  EExtern(fun a ->
  match a with
  | VInt n ->
    begin try f n with
    | Invalid_argument _ ->
      raise (RuntimeError "Printing of non char")
    end; VUnit
  | _ -> failwith "internal error")

let printType str =
  let extern = EExtern(fun a ->
    match a with
    | VUnit -> print_string str; VUnit
    | _ -> failwith "internal error")
  in
  EApp(make extern, [make EUnit])

let readInt =
  EExtern (fun a ->
  match a, read_int_opt () with
  | VUnit, Some n -> VInt n
  | VUnit, None -> raise (RuntimeError "Couldn't read int")
  | _, _ -> failwith "internal error")


module StringMap = Map.Make(String)

let builtins = [
    "add",  int2int_fun ( + );
    "sub",  int2int_fun ( - );
    "mult", int2int_fun ( * );
    "div",  int2int_fun ( / );
    "eq",   int2bool_fun ( = );
    "le",   int2bool_fun ( <= );
    "not",  bool1bool_fun ( not );
    "and",  bool2bool_fun ( && );
    "or",  bool2bool_fun ( || );
    "fst",  pair_fun ( fst );
    "snd",  pair_fun ( snd );
    "readInt",    readInt;
    "printInt",   int1unit_fun print_int;
    "printAscii", int1unit_fun (fun n -> Char.chr n |> print_char);
    (* "printType" *)
    (* printType requires special handling so it wont be here *)
] |> StringMap.of_list

let lookup_builtin str =
  StringMap.find str builtins

let lookup_builtin_opt str =
  StringMap.find_opt str builtins
