open Core.Imast
open Core

module UVar = Tvar.Make()
module TVar = Tvar.Make()
module TVarSet = TVar.MakeSet()
module TVarMap = TVar.MakeMap()

type t = view

and uvar_value =
  | Realised of t
  | Unrealised of Level.t

and uvar_struct = {
  id: UVar.t;
  value: uvar_value;
}

and uvar = uvar_struct ref
and view =
  | TUnit
  | TEmpty
  | TBool
  | TInt
  | TVar   of TVar.t
  | TADT   of IMAstVar.t * Level.t * t list
  | TUVar  of uvar
  | TArrow of Effect.uvar * t * t
  | TPair  of t * t

exception Cannot_compare of t * t
exception Levels_difference of IMAstVar.t * Level.t * Level.t

let t_unit  = TUnit
let t_empty = TEmpty
let t_bool  = TBool
let t_int   = TInt
let t_var x = TVar x
let t_arrow eff tps tp2 =
  let uv = Effect.fresh_uvar () in
  Effect.set_uvar uv eff;
  TArrow(uv, tps, tp2)
let t_arrow_uvar uv tps tp2 = TArrow(uv, tps, tp2)
let t_adt name level tps = TADT(name, level, tps)
let t_pair tp1 tp2 = TPair(tp1, tp2)

let fresh_tvar () = TVar (TVar.fresh ())
