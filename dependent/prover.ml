let () = Printexc.record_backtrace true

type var = string
(** Variables. *)

(** Expressions. *)
type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr

let rec to_string e =
  match e with
  | Type -> "type"
  | Var x -> x
  | App (u, v) -> to_string u ^ " " ^ to_string v
  | Abs (x, t, u) ->
      "(fun (" ^ x ^ " : " ^ to_string t ^ ") -> " ^ to_string u ^ ")"
  | Pi (x, a, b) -> "Pi(" ^ x ^ ", " ^ to_string a ^ ", " ^ to_string b ^ ")"
  | _ -> assert false

let n = ref 0

let fresh_var () =
  let x = "x" ^ string_of_int !n in
  incr n;
  x

let rec subst x t u =
  match t with
  | Type -> Type
  | Var y when y = x -> u
  | Var y -> Var y
  | App (v, w) -> App (subst x v u, subst x w u)
  | Abs (y, ty, v) ->
      let y' = fresh_var () in
      let v' = subst y v (Var y') in
      Abs (y', ty, subst x v' u)
  | Pi (y, a, b) ->
      let y' = fresh_var () in
      let b' = subst y b (Var y') in
      Pi (y', a, subst x b' u)
  | _ -> assert false

type context = (var * (expr * expr option)) list

let rec string_of_context ctx =
  match ctx with
  | [] -> ()
  | (x, (t, v)) :: l ->
      let st = to_string t in
      let sv = match v with None -> "" | Some v -> " = " ^ to_string v in
      print_endline (x ^ " : " ^ st ^ sv);
      string_of_context l

(* We assume these functions are only called with well-typed expressions. *)

(** Returns None if no reduction could be done, else returns reduced expr. *)
let rec red ctx e =
  match e with
  | Type -> None
  | Var x -> (
      match List.assoc_opt x ctx with
      | None -> None
      | Some (_, None) -> None
      | Some (_, Some v) -> Some v)
  | App (u, v) -> (
      match (red ctx u, red ctx v) with
      | None, None -> None
      | Some u', None -> Some (App (u', v))
      | None, Some v' -> Some (App (u, v'))
      | Some u', Some v' -> Some (App (u', v')))
  | Abs (x, tx, v) -> (
      match (red ctx tx, red ((x, (tx, None)) :: ctx) v) with
      | None, None -> None
      | Some tx', None -> Some (Abs (x, tx', v))
      | None, Some v' -> Some (Abs (x, tx, v'))
      | Some tx', Some v' -> Some (Abs (x, tx', v')))
  | Pi (x, a, b) -> (
      match (red ctx a, red ctx b) with
      | None, None -> None
      | Some a', None -> Some (Pi (x, a', b))
      | None, Some b' -> Some (Pi (x, a, b'))
      | Some a', Some b' -> Some (Pi (x, a', b')))
  | _ -> assert false

let rec normalize ctx e =
  match red ctx e with None -> e | Some u -> normalize ctx u
