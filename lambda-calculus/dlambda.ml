open Lambda
open Format

type dvar = int

type db =
  | DVar of dvar
  | DApp of db * db
  | DAbs of db

let rec to_string : db -> string = function
  | DVar dv ->
    sprintf "%i" dv
  | DApp (t1, t2) ->
    sprintf "(%s %s)" (to_string t1) (to_string t2)
  | DAbs t ->
    sprintf "(λ.%s)" (to_string t)

let db_of_term : t -> db =
  let rec aux : var list -> t -> db = fun dl -> function
    | Var v ->
      (match List.find_index (String.equal v) dl with
      | Some dv ->
        DVar dv
      | None ->
        assert false)
    | App (t1, t2) ->
      DApp (aux dl t1, aux dl t2)
    | Abs (v, t) ->
      DAbs (aux (v :: dl) t)
  in
  aux []

let () =
  let t = Abs ("x", Abs ("y", App (App (Var "x", Abs ("z", Var "x")), Abs ("x", App (Var "x", Var "y"))))) in
  let t' = DAbs (DAbs (DApp (DApp (DVar 1, DAbs (DVar 2)), DAbs (DApp (DVar 0, DVar 1))))) in
  assert (db_of_term t = t')

let rec lift : int -> db -> db = fun dv -> function
  | DVar dv' ->
    DVar (if dv' >= dv then (dv' + 1) else dv')
  | DApp (t1, t2) ->
    DApp (lift dv t1, lift dv t2)
  | DAbs t ->
    DAbs (lift (dv + 1) t)

let () =
  let t = lift 0 (DAbs (DApp (DVar 0, DVar 1))) in
  let t' = DAbs (DApp (DVar 0, DVar 2)) in
  assert (t = t')

let unlift : int -> dvar -> dvar = fun i dv ->
  if dv > i then (dv - 1) else dv

let () =
  assert (unlift 5 1 = 1);
  assert (unlift 5 4 = 4);
  assert (unlift 5 6 = 5);
  assert (unlift 5 9 = 8)

let rec unlift : int -> db -> db = fun dv -> function
  | DVar dv' ->
    DVar (if dv' > dv then (dv' - 1) else dv')
  | DApp (t1, t2) ->
    DApp (unlift dv t1, unlift dv t2)
  | DAbs t ->
    DAbs (unlift (dv + 1) t)

let rec sub : int -> db -> db -> db = fun x u -> function
  | DVar v as t ->
    if Int.equal x v
    then u
    else t
  | DApp (t1, t2) ->
    DApp (sub x u t1, sub x u t2)
  | DAbs t ->
    DAbs (sub (x + 1) (lift 0 u) t)

let rec red : db -> db option = function
  | DApp (DAbs t1, t2) ->
    Some (sub 0 t2 (unlift 0 t1))
  | DApp (t1, t2) ->
    (match red t1 with
    | Some t1 ->
      Some (DApp (t1, t2))
    | None ->
      (match red t2 with
      | Some t2 ->
        Some (DApp (t1, t2))
      | None ->
        None))
  | DAbs t ->
    (match red t with
    | Some t ->
      Some (DAbs t)
    | None ->
      None)
  | DVar _ ->
    None

let rec dnormalize : db -> db = fun t ->
  match red t with
  | Some t ->
    dnormalize t
  | None ->
    t

let dreduction : db -> db = fun t ->
  let rec f : db -> db list = fun t ->
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

let eq : t -> t -> bool = fun t1 t2 ->
  dnormalize (db_of_term t1) = dnormalize (db_of_term t2)

let () =
  let id = Abs ("x", Var "x") in
  let id2 = App (id, id) in
  assert (eq (App (id2, id2)) id2)

let () =
  assert (eq (apps [add; nat 6; nat 5]) (nat 11))

let () =
  assert (eq (apps [mul; nat 3; nat 4]) (nat 12))

let () =
  assert (eq (apps [iszero; nat 5]) bfalse);
  assert (eq (apps [iszero; nat 0]) btrue)

let () =
  assert (eq (apps [pred_fun; apps [pair; nat 1; nat 5]]) (apps [pair; nat 5; nat 6]))

let () =
  assert (eq (apps [pred; nat 11]) (nat 10));
  assert (eq (apps [pred; nat 0]) (nat 0))

let () =
  assert (eq (apps [minus; nat 14; nat 5]) (nat 9))

let () =
  let t = db_of_term (apps [factorial; nat 4]) in
  let u = db_of_term (nat 24) in
  assert (dnormalize t = dnormalize u)
