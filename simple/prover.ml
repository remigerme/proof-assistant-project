let () = Printexc.record_backtrace true

(* Type variables *)
type tvar = string

(* Term variables *)
type var = string

(* Types *)
type ty = TTrue | TVar of tvar | TAbs of ty * ty | TProd of ty * ty

(* Terms *)
type tm =
  | True
  | Var of var
  | App of tm * tm
  | Abs of var * ty * tm
  | Prod of tm * tm
  | Fst of tm
  | Snd of tm

let rec string_of_ty t =
  match t with
  | TTrue -> "True"
  | TVar x -> x
  | TAbs (u, v) -> "(" ^ string_of_ty u ^ " => " ^ string_of_ty v ^ ")"
  | TProd (u, v) -> "(" ^ string_of_ty u ^ " /\\ " ^ string_of_ty v ^ ")"

let rec string_of_tm t =
  match t with
  | True -> "true"
  | Var x -> x
  | App (u, v) -> string_of_tm u ^ " " ^ string_of_tm v
  | Abs (x, tx, u) ->
      "(fun (" ^ x ^ " : " ^ string_of_ty tx ^ ") -> " ^ string_of_tm u ^ ")"
  | Prod (u, v) -> "(" ^ string_of_tm u ^ ", " ^ string_of_tm v ^ ")"
  | Fst u -> "fst (" ^ string_of_tm u ^ ")"
  | Snd u -> "snd (" ^ string_of_tm u ^ ")"

type context = (var * ty) list

exception Type_error

let rec infer_type gamma t =
  match t with
  | True -> TTrue
  | Var x -> ( try List.assoc x gamma with Not_found -> raise Type_error)
  | App (u, v) -> (
      match infer_type gamma u with
      | TAbs (tu, turet) ->
          check_type gamma v tu;
          turet
      | _ -> raise Type_error)
  | Abs (x, tx, u) -> TAbs (tx, infer_type ((x, tx) :: gamma) u)
  | Prod (u, v) -> TProd (infer_type gamma u, infer_type gamma v)
  | Fst u -> (
      match infer_type gamma u with
      | TProd (tu, _) -> tu
      | _ -> raise Type_error)
  | Snd u -> (
      match infer_type gamma u with
      | TProd (_, tu) -> tu
      | _ -> raise Type_error)

and check_type gamma t ty =
  match infer_type gamma t with tt when tt = ty -> () | _ -> raise Type_error

(*********)
(* TESTS *)
(*********)

let () =
  let test_type = TAbs (TAbs (TVar "A", TVar "B"), TAbs (TVar "A", TVar "C")) in
  let s = string_of_ty test_type in
  print_endline s

let () =
  let test_term =
    Abs
      ( "f",
        TAbs (TVar "A", TVar "B"),
        Abs ("x", TVar "A", App (Var "f", Var "x")) )
  in
  let s = string_of_tm test_term in
  print_endline s

let () =
  let t =
    Abs
      ( "f",
        TAbs (TVar "A", TVar "B"),
        Abs
          ( "g",
            TAbs (TVar "B", TVar "C"),
            Abs ("x", TVar "A", App (Var "g", App (Var "f", Var "x"))) ) )
  in
  let ty =
    TAbs
      ( TAbs (TVar "A", TVar "B"),
        TAbs (TAbs (TVar "B", TVar "C"), TAbs (TVar "A", TVar "C")) )
  in
  assert (infer_type [] t = ty)

let () =
  let t = Abs ("f", TVar "A", Var "x") in
  try
    let _ = infer_type [] t in
    assert false
  with Type_error -> ()

let () =
  let t = Abs ("f", TVar "A", Abs ("x", TVar "B", App (Var "f", Var "x"))) in
  try
    let _ = infer_type [] t in
    assert false
  with Type_error -> ()

let () =
  let t =
    Abs
      ( "f",
        TAbs (TVar "A", TVar "B"),
        Abs ("x", TVar "B", App (Var "f", Var "x")) )
  in
  try
    let _ = infer_type [] t in
    assert false
  with Type_error -> ()

let () =
  let t = Abs ("x", TVar "A", Var "x") in
  let ty = TAbs (TVar "A", TVar "A") in
  check_type [] t ty

let () =
  let t = Abs ("x", TVar "A", Var "x") in
  let ty = TAbs (TVar "B", TVar "B") in
  try
    let _ = check_type [] t ty in
    assert false
  with Type_error -> ()

let () =
  try
    let _ = check_type [] (Var "x") (TVar "A") in
    assert false
  with Type_error -> ()

(*************)
(* WITNESSES *)
(*************)

let () =
  let and_comm =
    Abs ("p", TProd (TVar "A", TVar "B"), Prod (Snd (Var "p"), Fst (Var "p")))
  in
  print_endline (string_of_ty (infer_type [] and_comm))

let () =
  let eval = Abs ("f", TAbs (TTrue, TVar "A"), App (Var "f", True)) in
  print_endline (string_of_ty (infer_type [] eval))
