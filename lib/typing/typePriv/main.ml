open Core.Imast
open Core

module UVar = Tvar.Make()
module TVar = Tvar.Make()
module TVarSet = TVar.MakeSet()
module TVarMap = TVar.MakeMap()

type t =
  | TIUnit
  | TIEmpty
  | TIBool
  | TIInt
  | TIVar    of TVar.t
  | TIADT    of IMAstVar.t * Level.t * t list
  | TIUVar   of uvar
  | TIArrow  of t list * t
  | TIPair of t * t

and uvar_value =
  | Realised of t
  | Unrealised of Level.t

and uvar_struct = {
  id: UVar.t;
  value: uvar_value;

  (* gvar set means that it was created in abstraction application,
   *   is an arrow and can be generalised to arrow that takes more arguments.
   *
   * (τ1, τ2) -> (τ3, τ4) -> τ5
   *    =>
   * (τ1, τ2, τ3, τ4) -> τ5
   *)
  is_gvar: bool;
}

and uvar = uvar_struct ref
and view =
  | TUnit
  | TEmpty
  | TBool
  | TInt
  | TVar    of TVar.t
  | TADT    of IMAstVar.t * Level.t * t list
  | TGVar   of uvar * view option
  | TUVar   of uvar
  | TArrow  of t list * t
  | TPair of t * t

exception Cannot_compare of t * t

let t_unit  = TIUnit
let t_empty = TIEmpty
let t_bool  = TIBool
let t_int   = TIInt
let t_var x = TIVar x
let t_arrow tps tp2 = TIArrow(tps, tp2)
let t_adt name level tps = TIADT(name, level, tps)
let t_pair tp1 tp2 = TIPair(tp1, tp2)

let fresh_tvar () = TIVar (TVar.fresh ())
