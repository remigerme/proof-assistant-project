let () = Printexc.record_backtrace true

(* Type variables. *)
type tvar = string

(* Term variables. *)
type var = string

(** Types. *)
type ty = TVar of tvar | Arr of ty * ty

type tm = Var of var | App of tm * tm | Abs of var * ty * tm

let rec string_of_ty t =
  match t with
  | TVar x -> x
  | Arr (u, v) -> "(" ^ string_of_ty u ^ " => " ^ string_of_ty v ^ ")"

let rec string_of_tm t =
  match t with
  | Var x -> x
  | App (u, v) -> string_of_tm u ^ " " ^ string_of_tm v
  | Abs (x, tx, u) ->
      "(fun (" ^ x ^ " : " ^ string_of_ty tx ^ ") -> " ^ string_of_tm u ^ ")"

type context = (var * ty) list

exception Type_error

let rec infer_type' gamma t =
  match t with
  | Var x -> ( try List.assoc x gamma with Not_found -> raise Type_error)
  | App (u, v) -> (
      let tu = infer_type' gamma u in
      let tv = infer_type' gamma v in
      match tu with Arr (ta, tb) when ta = tv -> tb | _ -> raise Type_error)
  | Abs (x, tx, u) ->
      let tu = infer_type' ((x, tx) :: gamma) u in
      Arr (tx, tu)

let check_type' gamma t ty =
  match infer_type' gamma t with tt when tt = ty -> () | _ -> raise Type_error

(* TODO : MUTUALLY RECURSIVE DEFINITIONS *)

(*********)
(* TESTS *)
(*********)

let () =
  let test_type = Arr (Arr (TVar "A", TVar "B"), Arr (TVar "A", TVar "C")) in
  let s = string_of_ty test_type in
  print_endline s

let () =
  let test_term =
    Abs
      ( "f",
        Arr (TVar "A", TVar "B"),
        Abs ("x", TVar "A", App (Var "f", Var "x")) )
  in
  let s = string_of_tm test_term in
  print_endline s

let () =
  let t =
    Abs
      ( "f",
        Arr (TVar "A", TVar "B"),
        Abs
          ( "g",
            Arr (TVar "B", TVar "C"),
            Abs ("x", TVar "A", App (Var "g", App (Var "f", Var "x"))) ) )
  in
  let ty =
    Arr
      ( Arr (TVar "A", TVar "B"),
        Arr (Arr (TVar "B", TVar "C"), Arr (TVar "A", TVar "C")) )
  in
  assert (infer_type' [] t = ty)

let () =
  let t = Abs ("f", TVar "A", Var "x") in
  try
    let _ = infer_type' [] t in
    assert false
  with Type_error -> ()

let () =
  let t = Abs ("f", TVar "A", Abs ("x", TVar "B", App (Var "f", Var "x"))) in
  try
    let _ = infer_type' [] t in
    assert false
  with Type_error -> ()

let () =
  let t =
    Abs
      ( "f",
        Arr (TVar "A", TVar "B"),
        Abs ("x", TVar "B", App (Var "f", Var "x")) )
  in
  try
    let _ = infer_type' [] t in
    assert false
  with Type_error -> ()

let () =
  let t = Abs ("x", TVar "A", Var "x") in
  let ty = Arr (TVar "A", TVar "A") in
  check_type' [] t ty

let () =
  let t = Abs ("x", TVar "A", Var "x") in
  let ty = Arr (TVar "B", TVar "B") in
  try
    let _ = check_type' [] t ty in
    assert false
  with Type_error -> ()

let () =
  try
    let _ = check_type' [] (Var "x") (TVar "A") in
    assert false
  with Type_error -> ()
