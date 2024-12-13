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
      "(Ind " ^ to_string p ^ " " ^ to_string z ^ " " ^ to_string s ^ " "
      ^ to_string n ^ ")"
  | Eq (t, u) -> "(" ^ to_string t ^ " = " ^ to_string u ^ ")"
  | Refl t -> "(refl " ^ to_string t ^ ")"
  | J (p, r, x, y, e) ->
      "(J " ^ to_string p ^ " " ^ to_string r ^ " " ^ to_string x ^ " "
      ^ to_string y ^ " " ^ to_string e ^ ")"

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
  | Eq (v, w) -> Eq (subst x t v, subst x t w)
  | Refl v -> Refl (subst x t v)
  | J (p, r, y, y', e) ->
      J (subst x t p, subst x t r, subst x t y, subst x t y', subst x t e)

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
          | _ -> None)
      | Some n' -> Some n')
  | Eq (t, u) -> (
      match (red ctx t, red ctx u) with
      | None, None -> None
      | Some t', None -> Some (Eq (t', u))
      | None, Some u' -> Some (Eq (t, u'))
      | Some t', Some u' -> Some (Eq (t', u')))
  | Refl t -> ( match red ctx t with None -> None | Some t' -> Some (Refl t'))
  | J (_, r, x, y, e) when x = y && e = Refl x -> Some (App (r, x))
  | J (p, r, x, y, e) -> (
      match (red ctx p, red ctx r, red ctx x, red ctx y, red ctx e) with
      | None, None, None, None, None -> None
      | Some p', _, _, _, _ -> Some (J (p', r, x, y, e))
      | _, Some r', _, _, _ -> Some (J (p, r', x, y, e))
      | _, _, Some x', _, _ -> Some (J (p, r, x', y, e))
      | _, _, _, Some y', _ -> Some (J (p, r, x, y', e))
      | _, _, _, _, Some e' -> Some (J (p, r, x, y, e')))

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
  | Eq (t, u), Eq (t', u') -> alpha t t' && alpha u u'
  | Refl t, Refl t' -> alpha t t'
  | J (p, r, x, y, e), J (p', r', x', y', e') ->
      alpha p p' && alpha r r' && alpha x x' && alpha y y' && alpha e e'
  | _ -> false

let conv ctx t u =
  let t' = normalize ctx t in
  let u' = normalize ctx u in
  alpha t' u'

exception Type_error of string

(** Utils for readability *)
let err s = raise (Type_error s)

let rec infer ctx e =
  match e with
  | Type -> Type
  | Var x -> (
      match List.assoc_opt x ctx with
      | Some (t, _) -> t
      | None -> err ("Unkown type for variable " ^ x))
  | App (u, v) -> (
      let tu = infer ctx u in
      let tv = infer ctx v in
      match tu with
      | Pi (x, tx, w) when conv ctx tx tv -> subst x v w
      | _ ->
          err
            ("Term of type " ^ to_string tv ^ " is applied to term of type "
           ^ to_string tu))
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
              else err ("Wrong type (2) for s : " ^ to_string ts)
          | _ -> err ("Wrong type (1) for s : " ^ to_string ts)
        else
          err
            ("z should be of type " ^ to_string pz ^ " but is of type "
           ^ to_string tz)
      else err ("Invalid type for p which is of type " ^ to_string tp)
  | Eq (_, _) -> Type
  | Refl t -> Eq (t, t)
  | J (p, r, x, y, e) -> (
      (* Checking type of p (1) *)
      let tp = infer ctx p in
      match tp with
      | Pi (a, tx, w) -> (
          (match w with
          | Pi (b, tx', z) ->
              if conv ctx tx tx' then
                if
                  conv
                    ((b, (tx', None)) :: (a, (tx, None)) :: ctx)
                    z
                    (Pi ("", Eq (Var a, Var b), Type))
                then () (* Type of p is fine *)
                else err ("Invalid type for p (4) : " ^ to_string z)
              else
                err ("Invalid type for p (3) : " ^ to_string tx ^ to_string tx')
          | _ -> err ("Invalid type for p (2) : " ^ to_string w));
          (* Checking type of x and y *)
          check ctx x tx;
          check ctx y tx;
          (* Checking type of r *)
          let tr = infer ctx r in
          match tr with
          | Pi (x', tx', ro) ->
              if conv ctx tx tx' then
                let eval_refl =
                  App (App (App (p, Var x'), Var x'), Refl (Var x'))
                in
                if conv ((x', (tx, None)) :: ctx) ro eval_refl then
                  (* Checking type of e *)
                  let te = infer ctx e in
                  if conv ctx (Eq (x, y)) te then
                    (* Fiuh, everything's fine ! *)
                    normalize ctx (App (App (App (p, x), y), e))
                  else err ("Invalid type for e : " ^ to_string te)
                else err ("Invalid return type for r : " ^ to_string ro)
              else err ("Invalid input type for r : " ^ to_string tx')
          | _ -> err ("Invalid type for r : " ^ to_string tr))
      | _ -> err ("Invalid type for p (1) : " ^ to_string tp))

and check ctx e t =
  let it = infer ctx e in
  if not (conv ctx it t) then
    raise
      (Type_error
         ("Inferred type (" ^ to_string it ^ ") doesn't match expected type ("
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
