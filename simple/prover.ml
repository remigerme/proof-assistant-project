let () = Printexc.record_backtrace true

(* Print all the tests if set to true *)
let debug = false

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
  | Nat -> "N"

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
  | Zero -> "zero"
  | Suc n -> "suc(" ^ string_of_tm n ^ ")"
  | Rec (t, u, x, y, v) ->
      "rec(" ^ string_of_tm t ^ ", " ^ string_of_tm u ^ ", " ^ x ^ ", " ^ y
      ^ ", " ^ string_of_tm v ^ ")"

type context = (var * ty) list

exception Type_error

let rec infer_type ctx t =
  match t with
  | Unit -> TUnit
  | Empty (u, ta) ->
      check_type ctx u TEmpty;
      ta
  | Var x -> ( try List.assoc x ctx with Not_found -> raise Type_error)
  | App (u, v) -> (
      match infer_type ctx u with
      | TAbs (tu, turet) ->
          check_type ctx v tu;
          turet
      | _ -> raise Type_error)
  | Abs (x, tx, u) -> TAbs (tx, infer_type ((x, tx) :: ctx) u)
  | Prod (u, v) -> TProd (infer_type ctx u, infer_type ctx v)
  | Fst u -> (
      match infer_type ctx u with TProd (tu, _) -> tu | _ -> raise Type_error)
  | Snd u -> (
      match infer_type ctx u with TProd (_, tu) -> tu | _ -> raise Type_error)
  | Coprod (t, x, u, y, v) -> (
      match infer_type ctx t with
      | TCoprod (ta, tb) ->
          let tu = infer_type ((x, ta) :: ctx) u in
          let tv = infer_type ((y, tb) :: ctx) v in
          if tu = tv then tu else raise Type_error
      | _ -> raise Type_error)
  | Left (a, tb) -> TCoprod (infer_type ctx a, tb)
  | Right (ta, b) -> TCoprod (ta, infer_type ctx b)
  | Zero -> Nat
  | Suc n ->
      check_type ctx n Nat;
      Nat
  | Rec (t, u, x, y, v) ->
      check_type ctx t Nat;
      let tu = infer_type ctx u in
      check_type ((x, Nat) :: (y, tu) :: ctx) v tu;
      tu

and check_type ctx t ty =
  match infer_type ctx t with tt when tt = ty -> () | _ -> raise Type_error

(*********************************)
(* TOWARDS AN INTERACTIVE PROVER *)
(*********************************)

let string_of_ctx ctx =
  String.concat ", " (List.map (fun (x, tx) -> x ^ " : " ^ string_of_ty tx) ctx)

type sequent = context * ty

let string_of_seq (ctx, tx) = string_of_ctx ctx ^ " |- " ^ string_of_ty tx

let rec prove env a =
  print_endline (string_of_seq (env, a));
  print_string "? ";
  flush_all ();
  let error e =
    print_endline e;
    prove env a
  in
  let cmd, arg =
    let cmd = input_line stdin in
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    (c, a)
  in
  (* TODO : save cmds in a file *)
  match cmd with
  | "intro" -> (
      match a with
      | TAbs (a, b) ->
          if arg = "" then error "Please provide an argument for intro."
          else
            let x = arg in
            let t = prove ((x, a) :: env) b in
            Abs (x, a, t)
      | TProd (a, b) ->
          let t = prove env a in
          let u = prove env b in
          Prod (t, u)
      | TUnit -> Unit
      | Nat ->
          if arg = "zero" then Zero
          else if arg = "suc" then
            let t = prove env Nat in
            Suc t
          else error "Please provide an argument for intro (zero or suc)."
      | _ -> error "Don't know how to introduce this.")
  | "exact" ->
      if arg = "" then error "Please provide an argument for exact."
      else
        let t = tm_of_string arg in
        if infer_type env t <> a then error "Not the right type." else t
  | "elim" -> (
      if arg = "" then error "Please provide an argument for elim."
      else
        let x = arg in
        try
          match infer_type env (Var x) with
          | TAbs (y, b) when a = b ->
              let t = prove env y in
              App (Var x, t)
          | TCoprod (b, c) ->
              let t = prove ((x, b) :: env) a in
              let u = prove ((x, c) :: env) a in
              Coprod (Var x, x, t, x, u)
          | TEmpty -> Empty (Var x, a)
          | Nat ->
              print_endline "base case : ";
              let t = prove env a in
              print_endline "rec case : ";
              let u = prove (("prec", a) :: ("nrec", Nat) :: env) a in
              Rec (Var x, t, "nrec", "prec", u)
          | _ -> error "Don't know how to elim using the given term."
        with Type_error -> error "This term does not exist. Couldn't elim.")
  | "cut" ->
      if arg = "" then error "Please provide an argument for cut."
      else
        let tc = ty_of_string arg in
        let t = prove env (TAbs (tc, a)) in
        let u = prove env tc in
        App (t, u)
  | "fst" -> (
      if arg = "" then error "Please provide an argument for fst."
      else
        let x = Var arg in
        try
          match infer_type env x with
          | TProd (b, _) -> if a = b then Fst x else error "Wrong type."
          | _ -> error "Don't know how to use fst on the given variable."
        with Type_error -> error "This variable does not exist. Couldn't fst.")
  | "snd" -> (
      if arg = "" then error "Please provide an argument for snd."
      else
        let x = Var arg in
        try
          match infer_type env x with
          | TProd (_, b) -> if a = b then Snd x else error "Wrong type."
          | _ -> error "Don't know how to use snd on the given variable."
        with Type_error -> error "This variable does not exist. Couldn't snd.")
  | "left" -> (
      match a with
      | TCoprod (b, c) ->
          let t = prove env b in
          Left (t, c)
      | _ -> error "Don't know how to left on the current goal.")
  | "right" -> (
      match a with
      | TCoprod (b, c) ->
          let t = prove env c in
          Right (b, t)
      | _ -> error "Don't know how to right on the current goal.")
  | cmd -> error ("Unknown command: " ^ cmd)

let () =
  try
    print_endline "Please enter the formula to prove:";
    let a = input_line stdin in
    let a = ty_of_string a in
    print_endline "Let's prove it.";
    let t = prove [] a in
    print_endline "done.";
    print_endline "Proof term is";
    print_endline (string_of_tm t);
    print_string "Typechecking... ";
    flush_all ();
    assert (infer_type [] t = a);
    print_endline "ok."
  with
  | End_of_file -> print_endline "Input ended. Please provide a valid formula."
  | ex -> print_endline ("An error occured : " ^ Printexc.to_string ex)

(***************)
(* FIRST TESTS *)
(***************)

let first_tests () =
  if debug then
    let () =
      let test_type =
        TAbs (TAbs (TVar "A", TVar "B"), TAbs (TVar "A", TVar "C"))
      in
      let s = string_of_ty test_type in
      print_endline s
    in

    let () =
      let test_term =
        Abs
          ( "f",
            TAbs (TVar "A", TVar "B"),
            Abs ("x", TVar "A", App (Var "f", Var "x")) )
      in
      let s = string_of_tm test_term in
      print_endline s
    in

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
    in

    let () =
      let t = Abs ("f", TVar "A", Var "x") in
      try
        let _ = infer_type [] t in
        assert false
      with Type_error -> ()
    in

    let () =
      let t =
        Abs ("f", TVar "A", Abs ("x", TVar "B", App (Var "f", Var "x")))
      in
      try
        let _ = infer_type [] t in
        assert false
      with Type_error -> ()
    in

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
    in

    let () =
      let t = Abs ("x", TVar "A", Var "x") in
      let ty = TAbs (TVar "A", TVar "A") in
      check_type [] t ty
    in

    let () =
      let t = Abs ("x", TVar "A", Var "x") in
      let ty = TAbs (TVar "B", TVar "B") in
      try
        let _ = check_type [] t ty in
        assert false
      with Type_error -> ()
    in

    let () =
      try
        let _ = check_type [] (Var "x") (TVar "A") in
        assert false
      with Type_error -> ()
    in
    ()
  else ()

(*************)
(* WITNESSES *)
(*************)

let () =
  if debug then
    let () =
      let and_comm =
        Abs
          ("p", TProd (TVar "A", TVar "B"), Prod (Snd (Var "p"), Fst (Var "p")))
      in
      print_endline (string_of_ty (infer_type [] and_comm))
    in

    let () =
      let eval = Abs ("f", TAbs (TUnit, TVar "A"), App (Var "f", Unit)) in
      print_endline (string_of_ty (infer_type [] eval))
    in

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
    in

    let () =
      let expl =
        Abs
          ( "f",
            TProd (TVar "A", TAbs (TVar "A", TEmpty)),
            Empty (App (Snd (Var "f"), Fst (Var "f")), TVar "B") )
      in
      print_endline (string_of_ty (infer_type [] expl))
    in
    ()
  else ()

(****************)
(* PARSING TEST *)
(****************)

let () =
  if debug then
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
    in

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
    in
    ()
  else ()

(*********************)
(* INTERACTIVE TESTS *)
(*********************)

let () =
  if debug then
    let () =
      let ctx =
        [
          ("x", TAbs (TVar "A", TVar "B"));
          ("y", TProd (TVar "A", TVar "B"));
          ("Z", TVar "T");
        ]
      in
      print_endline (string_of_ctx ctx)
    in

    let () =
      let ctx = [ ("x", TAbs (TVar "A", TVar "B")); ("y", TVar "A") ] in
      let seq = (ctx, TVar "B") in
      print_endline (string_of_seq seq)
    in
    ()
  else ()
