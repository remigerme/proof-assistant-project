(* Type variables *)
type tvar = string

(* Term variables *)
type var = string

(* Types *)
type ty =
  | TUnit
  | TEmpty
  | TVar of tvar
  | TAbs of ty * ty
  | TProd of ty * ty
  | TCoprod of ty * ty
  | Nat

(* Terms *)
type tm =
  | Unit
  | Empty of tm * ty
  | Var of var
  | App of tm * tm
  | Abs of var * ty * tm
  | Prod of tm * tm
  | Fst of tm
  | Snd of tm
  | Coprod of tm * var * tm * var * tm
  | Left of tm * ty
  | Right of ty * tm
  | Zero
  | Suc of tm
  | Rec of tm * tm * var * var * tm
