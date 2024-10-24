open Format

type var = string

type t =
  | Var of var
  | App of t * t
  | Abs of var * t

let rec t_eqb : t -> t -> bool = fun t1 t2 ->
  match t1, t2 with
  | Var v1, Var v2 ->
    String.equal v1 v2
  | App (t11, t12), App (t21, t22) ->
    (t_eqb t11 t21) && (t_eqb t12 t22)
  | Abs (v1, t11), Abs (v2, t21) ->
    (String.equal v1 v2) && (t_eqb t11 t21)
  | _, _ ->
    false

let rec to_string : t -> string =
  let rec abs_list = function
    | Abs (v, t) ->
      let vl, t = abs_list t in
      v :: vl, t
    | t ->
      [ ], t
  in function
  | Var v ->
    sprintf "%s" v
  | App (t1, t2) ->
    sprintf "(%s %s)" (to_string t1) (to_string t2)
  | Abs _ as t ->
    let vl, t = abs_list t in
    sprintf "(λ%s.%s)" (String.concat "" vl) (to_string t)

let () =
  printf "%s\n" (to_string (Abs ("x", App (Var "y", Var "x"))));
  printf "%s\n" (to_string (App (Abs ("x", Var "y"), Var "x")))

let rec has_fv : var -> t -> bool = fun v -> function
  | Var v' ->
    String.equal v v'
  | App (t1, t2) ->
    (has_fv v t1) || (has_fv v t2)
  | Abs (v', t) ->
    (not (String.equal v v')) && (has_fv v t)

let () =
  let t = App (Var "x", Abs ("y", App (Var "y", Var "z"))) in
  assert (has_fv "x" t);
  assert (not (has_fv "y" t));
  assert (has_fv "z" t);
  assert (not (has_fv "w" t))

let fresh : unit -> var =
  let id = ref 0 in
  let f = fun () ->
    let x = "x" ^ string_of_int !id in
    id := !id + 1; x
  in f

let () =
  printf "%S\n" (fresh ());
  printf "%S\n" (fresh ());
  printf "%S\n" (fresh ())

let rec sub : var -> t -> t -> t = fun x u t ->
  match t with
  | Var v ->
    if String.equal x v
    then u
    else t
  | App (t1, t2) ->
    App (sub x u t1, sub x u t2)
  | Abs (v, t1) ->
    if String.equal x v
    then t
    else if has_fv v u
    then
      let fresh_var = fresh () in
      Abs (fresh_var, sub x u (sub v (Var fresh_var) t1))
    else Abs (v, sub x u t1)

let () =
  let t = App (Var "x", Abs ("y", Var "x")) in
  let i = Abs ("x", Var "x") in
  let ti = App (Abs ("x", Var "x"), Abs ("y", Abs ("x", Var "x"))) in
  assert (sub "x" i t = ti);
  assert (not (sub "x" (Var "y") (Abs ("y", Var "x")) = Abs("y", Var "y")))

let rec red : t -> t option = function
  | App (Abs (v, t1), t2) ->
    Some (sub v t2 t1)
  | App (t1, t2) as t ->
    (match red t1 with
    | Some t1 ->
      Some (App (t1, t2))
    | None ->
      (match red t2 with
      | Some t2 ->
        Some (App (t1, t2))
      | None ->
        None))
  | Abs (v, t) ->
    (match red t with
    | Some t ->
      Some (Abs (v, t))
    | None ->
      None)
  | Var _ ->
    None

let rec normalize : t -> t = fun t ->
  match red t with
  | Some t ->
    normalize t
  | None ->
    t

let reduction : t -> t = fun t ->
  let rec f : t -> t list = fun t ->
    match red t with
    | Some t' ->
      t :: f t'
    | None ->
      [ t ]
  in
  match f t with
  | [ ] ->
    assert false
  | t :: lt ->
    let step_cnt = List.length lt in
    printf "   %s\n" (to_string t);
    printf "%a\n"
      (pp_print_list ~pp_sep:pp_print_newline (fun fmt t -> fprintf fmt "-> %s" (to_string t))) lt;
    printf "%i reduction steps\n%!" step_cnt;
    List.nth lt (step_cnt - 1)

let _ =
  let id = Abs ("x", Var "x") in
  let id2 = App (id, id) in
  reduction (App (id2, id2))

let eq : t -> t -> bool = fun t1 t2 ->
  t_eqb (normalize t1) (normalize t2)

let () =
  let id = Abs ("x", Var "x") in
  let id2 = App (id, id) in
  assert (eq (App (id2, id2)) id2)

let rec alpha : t -> t -> bool = fun t1 t2 ->
  match t1, t2 with
  | Var v1, Var v2 ->
    String.equal v1 v2
  | App (t11, t12), App (t21, t22) ->
    (alpha t11 t21) && (alpha t12 t22)
  | Abs (v1, t11), Abs (v2, t21) ->
    let fresh_var = Var (fresh ()) in
    alpha (sub v1 fresh_var t11) (sub v2 fresh_var t21)
  | _, _ ->
    false

let () =
  assert (alpha (Abs ("x", Var "x")) (Abs ("y", Var "y")));
  assert (not (alpha (Abs ("x", Var "x")) (Abs ("x", Var "y"))))

let eq : t -> t -> bool = fun t1 t2 ->
  alpha (normalize t1) (normalize t2)

let () =
  let t = App (Abs ("x", Abs ("y", Var "x")), Var "y") in
  print_endline (to_string (normalize t));
  assert (eq t (Abs ("z", Var "y")))

let id : t = Abs ("x", Var "x")

let btrue : t = Abs ("x", Abs ("y", Var "x"))

let bfalse : t = Abs ("x", Abs ("y", Var "y"))

let rec abss : var list -> t -> t = function
  | [ ] ->
    fun t -> t
  | v :: vl ->
    fun t -> Abs (v, abss vl t)

let () =
  let t = Var "t" in
  assert (abss ["x"; "y"; "z"] t = Abs ("x", Abs ("y", Abs ("z", t))))

let rec apps : t list -> t = function
  | [ ] ->
    assert false
  | t :: tl ->
    List.fold_left (fun t1 t2 -> App (t1, t2)) t tl

let rec apps_right : t list -> t -> t = fun tl t ->
  List.fold_right (fun t1 t2 -> App (t1, t2)) tl t

let () =
  let t = Var "t" in
  let u = Var "u" in
  let v = Var "v" in
  let w = Var "w" in
  assert (apps [t; u; v; w] = App (App (App (t, u), v), w))

let bif : t =
  abss [ "c" ; "t" ; "f" ]
    (apps [ Var "c" ; Var "t" ; Var "f" ])

let () =
  let t = Var "t" in
  let u = Var "u" in
  assert (eq (apps [bif; btrue; t; u]) t);
  assert (eq (apps [bif; bfalse; t; u]) u)

let rec nat : int -> t = fun i ->
  abss [ "f" ; "x" ]
    (apps_right (List.init i (fun _ -> Var "f")) (Var "x"))

let succ : t =
  abss [ "n" ; "f" ; "x" ]
    (App (Var "f", apps [ Var "n" ; Var "f" ; Var "x" ]))

let () =
  assert (eq (apps [succ; nat 5]) (nat 6))

let add : t =
  abss [ "n" ; "m" ; "f" ; "x" ]
    (apps [ Var "n" ; Var "f" ; apps [ Var "m" ; Var "f" ; Var "x" ] ])

let () =
  assert (eq (apps [add; nat 6; nat 5]) (nat 11))

let mul : t =
  abss [ "m" ; "n" ; "f" ; "x" ]
    (apps [ Var "m" ; apps [ Var "n" ; Var "f" ] ; Var "x" ])

let () =
  assert (eq (apps [mul; nat 3; nat 4]) (nat 12))

let _ =
  reduction (apps [mul; nat 3; nat 4])

let _ =
  reduction (apps [mul; nat 1; nat 5])

let _ =
  reduction (apps [mul; nat 5; nat 1])

(* The number of resuction steps of [mul m n] is 4 + 2 * m *)

let iszero : t =
  let fresh_var = fresh () in
  abss [ "n" ]
    (apps [ Var "n" ; Abs (fresh_var, bfalse) ; btrue ])

let () =
  assert (eq (apps [iszero; nat 5]) bfalse);
  assert (eq (apps [iszero; nat 0]) btrue)

let pair : t =
  abss [ "x" ; "y" ; "f" ]
    (apps [ Var "f" ; Var "x" ; Var "y" ])

let fst : t =
  abss [ "p" ]
    (apps [ Var "p" ; btrue ])

let snd : t =
  abss [ "p" ]
    (apps [ Var "p" ; bfalse ])

let () =
  let t = Var "t" in
  let u = Var "u" in
  assert (eq (apps [fst; apps [pair; t; u]]) t);
  assert (eq (apps [snd; apps [pair; t; u]]) u)

let rec fib_naive : int -> int = fun n ->
  match n with
  | 0 -> 0
  | 1 -> 1
  | _ -> fib_naive (n - 1) + fib_naive (n - 2)

let () = assert (fib_naive 10 = 55)

(* The complexity of [fib_naive n] is exponential *)

let rec fib_fun : int * int -> int * int =
  fun (n, m) -> (m, n + m)

let fib = fun n ->
  let rec applyn init f n =
    match n with
    | 0 -> init
    | _ -> applyn (f init) f (n - 1)
  in
  Stdlib.fst (applyn (0, 1) fib_fun n)

let () = assert (fib 10 = 55)

let pred_fun : t =
  abss [ "p" ]
    (apps [ pair ; apps [ snd ; Var "p" ] ; apps [ succ ; apps [ snd ; Var "p" ] ] ])

let () =
  assert (eq (apps [pred_fun; apps [pair; nat 1; nat 5]]) (apps [pair; nat 5; nat 6]))

(*

pred_fun (p, q) = (q, q + 1)
pred_fun (pred_fun (p, q)) = (q + 1, q + 2)
pred_fun (pred_fun (pred_fun (p, q))) = (q + 2, q + 3)

pred_fun applied n times to (p, q) equals (q + n - 1, q + n), provided n is non-zero

*)

let pred : t =
  abss [ "n" ]
    (apps [ fst ; apps [ Var "n" ; pred_fun ; apps [ pair ; nat 0 ; nat 0 ] ] ])

let () =
  assert (eq (apps [pred; nat 11]) (nat 10));
  assert (eq (apps [pred; nat 0]) (nat 0))

let minus : t =
  abss [ "m" ; "n" ]
    (apps [ Var "n" ; pred ; Var "m" ])

let () =
  assert (eq (apps [minus; nat 14; nat 5]) (nat 9))

let fact_fun : (int -> int) -> int -> int = fun f n ->
  match n with
  | 0 -> 1
  | _ -> n * f (n - 1)

let rec fix f = fun n -> f (fix f) n

let fact = fix fact_fun

let () = assert (fact 5 = 120)

let fixpoint : t =
  Abs ("f", App (Abs ("x", App (Var "f", App (Var "x", Var "x"))), Abs ("x", App (Var "f", App (Var "x", Var "x")))))

let factorial : t =
  App (fixpoint,
  abss [ "f" ; "n" ]
    (apps [ bif ; apps [ iszero ; Var "n" ] ; nat 1 ; apps [ mul ; Var "n" ; apps [ Var "f" ; apps [ pred ; Var "n" ] ] ] ]))

let () = assert (eq (App (factorial, nat 5)) (nat 120))

let rec eta_reduction : t -> t option = function
  | Abs (v1, App (t, Var v2)) when String.equal v1 v2 ->
    Some t
  | Var _ ->
    None
  | Abs (v, t) ->
    (match eta_reduction t with
    | Some t ->
      Some (Abs (v, t))
    | None ->
      None)
  | App (t1, t2) ->
    (match eta_reduction t1 with
    | Some t1 ->
      Some (App (t1, t2))
    | None ->
      (match eta_reduction t2 with
      | Some t2 ->
        Some (App (t1, t2))
      | None ->
        None))

let rec eta : t -> t = fun t ->
  match eta_reduction t with
  | None -> t
  | Some t -> eta t

let etaeq : t -> t -> bool = fun t1 t2 ->
  alpha (normalize (eta t1)) (normalize (eta t2))

let () =
  let t = (Abs ("x", App (Abs ("y", Abs ("z", App (Var "y", Var "z"))), Var "x"))) in
  let u = Abs ("t", Var "t") in
  assert (etaeq t u)
