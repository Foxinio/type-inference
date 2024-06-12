open Ast
open Core

open Imast

type t = {
  varname : string VarTbl.t;
  ctors   : (int * var_type) VarMap.t;
  adts    : int VarMap.t VarMap.t;
}

let empty = {
  varname = VarTbl.create 11;
  adts    = VarMap.empty;
  ctors   = VarMap.empty;
}

let of_varname_tbl tbl = {
  varname = tbl;
  ctors   = VarMap.empty;
  adts    = VarMap.empty;
}

let lookup_var env x = unimplemented ()

let add_ctors env keys tp =
  let values = Seq.zip (Seq.ints 0) (Seq.repeat tp) in
  let ctors_seq = Seq.zip keys values in
  let ctors = VarMap.add_seq ctors_seq env.ctors in
  { env with ctors }

let lookup_ctor env sysF_ctor =
  VarMap.find sysF_ctor env.ctors

let to_varname_seq env =
  VarTbl.to_seq env

