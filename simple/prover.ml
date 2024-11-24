let () = Printexc.record_backtrace true

open Expr

let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)
let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)

let rec string_of_ty t =
  match t with
  | TUnit -> "unit"
  | TEmpty -> "empty"
  | TVar x -> x
  | TAbs (u, v) -> "(" ^ string_of_ty u ^ " => " ^ string_of_ty v ^ ")"
  | TProd (u, v) -> "(" ^ string_of_ty u ^ " /\\ " ^ string_of_ty v ^ ")"
  | TCoprod (u, v) -> "(" ^ string_of_ty u ^ " \\/ " ^ string_of_ty v ^ ")"

let rec string_of_tm t =
  match t with
  | Unit -> "()"
  | Empty (u, ta) -> "absurd(" ^ string_of_tm u ^ ", " ^ string_of_ty ta ^ ")"
  | Var x -> x
  | App (u, v) -> string_of_tm u ^ " " ^ string_of_tm v
  | Abs (x, tx, u) ->
      "(fun (" ^ x ^ " : " ^ string_of_ty tx ^ ") -> " ^ string_of_tm u ^ ")"
  | Prod (u, v) -> "(" ^ string_of_tm u ^ ", " ^ string_of_tm v ^ ")"
  | Fst u -> "fst(" ^ string_of_tm u ^ ")"
  | Snd u -> "snd(" ^ string_of_tm u ^ ")"
  | Coprod (t, x, u, y, v) ->
      "case " ^ string_of_tm t ^ " of " ^ x ^ " -> " ^ string_of_tm u ^ " | "
      ^ y ^ " -> " ^ string_of_tm v
  | Left (a, tb) -> "left(" ^ string_of_tm a ^ ", " ^ string_of_ty tb ^ ")"
  | Right (ta, b) -> "right(" ^ string_of_ty ta ^ ", " ^ string_of_tm b ^ ")"

type context = (var * ty) list

exception Type_error

let rec infer_type gamma t =
  match t with
  | Unit -> TUnit
  | Empty (u, ta) ->
      check_type gamma u TEmpty;
      ta
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
  | Coprod (t, x, u, y, v) -> (
      match infer_type gamma t with
      | TCoprod (ta, tb) ->
          let tu = infer_type ((x, ta) :: gamma) u in
          let tv = infer_type ((y, tb) :: gamma) v in
          if tu = tv then tu else raise Type_error
      | _ -> raise Type_error)
  | Left (a, tb) -> TCoprod (infer_type gamma a, tb)
  | Right (ta, b) -> TCoprod (ta, infer_type gamma b)

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
  let eval = Abs ("f", TAbs (TUnit, TVar "A"), App (Var "f", Unit)) in
  print_endline (string_of_ty (infer_type [] eval))

let () =
  let or_comm =
    Abs
      ( "o",
        TCoprod (TVar "A", TVar "B"),
        Coprod
          ( Var "o",
            "x",
            Right (TVar "B", Var "x"),
            "y",
            Left (Var "y", TVar "A") ) )
  in
  print_endline (string_of_ty (infer_type [] or_comm))

let () =
  let non_contrad =
    Abs
      ( "f",
        TProd (TVar "A", TAbs (TVar "A", TEmpty)),
        Empty (App (Snd (Var "f"), Fst (Var "f")), TVar "B") )
  in
  print_endline (string_of_ty (infer_type [] non_contrad))

(****************)
(* PARSING TEST *)
(****************)
let () =
  let l =
    [
      "A => B";
      "A ⇒ B";
      "A /\\ B";
      "A ∧ B";
      "T";
      "A \\/ B";
      "A ∨ B";
      "_";
      "not A";
      "¬ A";
    ]
  in
  List.iter
    (fun s ->
      Printf.printf "the parsing of \"%s\" is %s\n%!" s
        (string_of_ty (ty_of_string s)))
    l

let () =
  let l =
    [
      "t u v";
      "fun (x : A) -> t";
      "λ (x : A) → t";
      "(t , u)";
      "fst(t)";
      "snd(t)";
      "()";
      "case t of x -> u | y -> v";
      "left(t,B)";
      "right(A,t)";
      "absurd(t,A)";
    ]
  in
  List.iter
    (fun s ->
      Printf.printf "the parsing of \"%s\" is %s\n%!" s
        (string_of_tm (tm_of_string s)))
    l
