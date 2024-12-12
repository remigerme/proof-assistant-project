let () = Printexc.record_backtrace true

open Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)

let rec to_string e =
  match e with
  | Type -> "type"
  | Var x -> x
  | App (u, v) -> "(" ^ to_string u ^ " " ^ to_string v ^ ")"
  | Abs (x, t, u) ->
      "(fun (" ^ x ^ " : " ^ to_string t ^ ") -> " ^ to_string u ^ ")"
  | Pi (x, a, b) -> "((" ^ x ^ " : " ^ to_string a ^ ") -> " ^ to_string b ^ ")"
  | Nat -> "N"
  | Z -> "Z"
  | S n -> "(S " ^ to_string n ^ ")"
  | Ind (p, z, s, n) ->
      "ind(" ^ to_string p ^ ", " ^ to_string z ^ ", " ^ to_string s ^ ", "
      ^ to_string n ^ ")"
  | _ -> assert false

let n = ref 0

let fresh_var () =
  let x = "x" ^ string_of_int !n in
  incr n;
  x

(** Substitutes x by t in u. *)
let rec subst x t u =
  match u with
  | Type -> Type
  | Var y when y = x -> t
  | Var y -> Var y
  | App (v, w) -> App (subst x t v, subst x t w)
  | Abs (y, ty, v) ->
      let y' = fresh_var () in
      let v' = subst y (Var y') v in
      Abs (y', subst x t ty, subst x t v')
  | Pi (y, a, b) ->
      let y' = fresh_var () in
      let b' = subst y (Var y') b in
      Pi (y', subst x t a, subst x t b')
  | Nat -> Nat
  | Z -> Z
  | S n -> S (subst x t n)
  | Ind (p, z, s, n) -> Ind (subst x t p, subst x t z, subst x t s, subst x t n)
  | _ -> assert false

type context = (var * (expr * expr option)) list

let rec string_of_context ctx =
  match ctx with
  | [] -> ""
  | (x, (t, v)) :: l ->
      let st = to_string t in
      let sv = match v with None -> "" | Some v -> " = " ^ to_string v in
      let endline = if List.length l > 0 then "\n" else "" in
      x ^ " : " ^ st ^ sv ^ endline ^ string_of_context l

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
  | App (Abs (x, _, u), t) -> Some (subst x t u)
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
  | Nat -> None
  | Z -> None
  | S n -> ( match red ctx n with None -> None | Some n' -> Some (S n'))
  | Ind (p, z, s, n) -> (
      match red ctx n with
      | None -> (
          match n with
          | Z -> Some z
          | S n' -> Some (App (App (s, n'), Ind (p, z, s, n')))
          | _ -> assert false (* n is not correctly typed *))
      | Some n' -> Some n')
  | _ -> assert false

let rec normalize ctx e =
  match red ctx e with None -> e | Some u -> normalize ctx u

let rec alpha t t' =
  match (t, t') with
  | Type, Type -> true
  | Var x, Var y when x = y -> true
  | App (u, v), App (u', v') -> alpha u u' && alpha v v'
  | Abs (x, tx, u), Abs (y, ty, v) ->
      let z = fresh_var () in
      let u' = subst x u (Var z) in
      let v' = subst y v (Var z) in
      alpha tx ty && alpha u' v'
  | Pi (x, a, b), Pi (y, c, d) ->
      let z = fresh_var () in
      let b' = subst x b (Var z) in
      let d' = subst y d (Var z) in
      alpha a c && alpha b' d'
  | Nat, Nat -> true
  | Z, Z -> true
  | S m, S n -> alpha m n
  | Ind (p, z, s, n), Ind (p', z', s', n') ->
      alpha p p' && alpha z z' && alpha s s' && alpha n n'
  | _ -> false

let conv ctx t u =
  let t' = normalize ctx t in
  let u' = normalize ctx u in
  alpha t' u'

exception Type_error of string

let rec infer ctx e =
  match e with
  | Type -> Type
  | Var x -> (
      match List.assoc_opt x ctx with
      | Some (t, _) -> t
      | None -> raise (Type_error ("Unkown type for variable " ^ x)))
  | App (u, v) -> (
      let tu = infer ctx u in
      let tv = infer ctx v in
      match tu with
      | Pi (x, tx, w) when conv ctx tx tv -> subst x v w
      | _ ->
          raise
            (Type_error
               ("Term of type " ^ to_string tv ^ " is applied to term of type "
              ^ to_string tu)))
  | Abs (x, tx, u) -> Pi (x, tx, infer ((x, (tx, None)) :: ctx) u)
  | Pi (_, _, _) -> Type
  | Nat -> Type
  | Z -> Nat
  | S n ->
      check ctx n Nat;
      Nat
  | Ind (p, z, s, n) ->
      (* Checking type of n *)
      check ctx n Nat;
      let tp = infer ctx p in
      (* Checkinf type of p *)
      if conv ctx tp (Pi ("", Nat, Type)) then
        let tz = infer ctx z in
        let pz = App (p, Z) in
        (* Checking type of z is p Z *)
        if conv ctx tz pz then
          let ts = infer ctx s in
          match ts with
          | Pi (n', c, d) when conv ctx c Nat ->
              if
                conv
                  ((n', (Nat, None)) :: ctx)
                  d
                  (Pi ("", App (p, Var n'), App (p, S (Var n'))))
              then normalize ctx (App (p, n))
              else raise (Type_error ("Wrong type (2) for s : " ^ to_string ts))
          | _ -> raise (Type_error ("Wrong type (1) for s : " ^ to_string ts))
        else
          raise
            (Type_error
               ("z should be of type " ^ to_string pz ^ " but is of type "
              ^ to_string tz))
      else
        raise
          (Type_error ("Invalid type for p which is of type " ^ to_string tp))
  | _ -> raise (Type_error "Not implemented yet")

and check ctx e t =
  let it = infer ctx e in
  if it <> t then
    raise
      (Type_error
         ("Inferred type ( " ^ to_string it ^ ") doesn't match expected type ("
        ^ to_string t ^ ")."))

(** Interactive loop *)
let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "interactive.proof" in
  let split c s =
    try
      let n = String.index s c in
      ( String.trim (String.sub s 0 n),
        String.trim (String.sub s (n + 1) (String.length s - (n + 1))) )
    with Not_found -> (s, "")
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd ^ "\n");
        print_endline cmd;
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
          let x, sa = split ':' arg in
          let a = of_string sa in
          check !env a Type;
          env := (x, (a, None)) :: !env;
          print_endline (x ^ " assumed of type " ^ to_string a)
      | "define" ->
          let x, st = split '=' arg in
          let t = of_string st in
          let a = infer !env t in
          env := (x, (a, Some t)) :: !env;
          print_endline
            (x ^ " defined to " ^ to_string t ^ " of type " ^ to_string a)
      | "context" -> print_endline (string_of_context !env)
      | "type" ->
          let t = of_string arg in
          let a = infer !env t in
          print_endline (to_string t ^ " is of type " ^ to_string a)
      | "check" ->
          let t, a = split '=' arg in
          let t = of_string t in
          let a = of_string a in
          check !env t a;
          print_endline "Ok."
      | "eval" ->
          let t = of_string arg in
          let _ = infer !env t in
          print_endline (to_string (normalize !env t))
      | "exit" -> loop := false
      | "" | "#" -> ()
      | cmd -> print_endline ("Unknown command: " ^ cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> print_endline ("Error: " ^ err ^ ".")
    | Type_error err -> print_endline ("Typing error :" ^ err ^ ".")
    | Parsing.Parse_error -> print_endline "Parsing error."
  done;
  print_endline "Bye."
