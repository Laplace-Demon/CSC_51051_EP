open Format

type typ =
  | TBool
  | TInt
  | TProd of typ * typ
  | TUnit

let rec typ_eqb typ1 typ2 =
  match typ1, typ2 with
  | TBool, TBool | TInt, TInt | TUnit, TUnit ->
    true
  | TProd (typ11, typ12), TProd (typ21, typ22) ->
    typ_eqb typ11 typ21
    && typ_eqb typ12 typ22
  | _, _ ->
    false

let rec pp_typ fmt = function
  | TBool ->
    fprintf fmt "bool"
  | TInt ->
    fprintf fmt "int"
  | TProd (t1, t2) ->
    fprintf fmt "(%a * %a)" pp_typ t1 pp_typ t2
  | TUnit ->
    fprintf fmt "unit"

type prog =
  (* Basics *)
  | Bool of bool
  | Int of int
  | Add of prog * prog
  | Lt of prog * prog
  | If of prog * prog * prog
  (* Products *)
  | Pair of prog * prog
  | Fst of prog
  | Snd of prog
  (* Unit *)
  | Unit
  (* Others *)
  | Let of string * prog * prog
  | Var of string

(* equivalence defined as structural *)

let rec prog_eqb p1 p2 =
  match p1, p2 with
  | Bool b1, Bool b2 ->
    Bool.equal b1 b2
  | Int i1, Int i2 ->
    Int.equal i1 i2
  | Add (p11, p12), Add (p21, p22)
  | Lt (p11, p12), Lt (p21, p22)
  | Pair (p11, p12), Pair (p21, p22) ->
    prog_eqb p11 p21
    && prog_eqb p12 p22
  | If (c1, p11, p12), If (c2, p21, p22) ->
    prog_eqb c1 c2
    && prog_eqb p11 p21
    && prog_eqb p12 p22
  | Fst p11, Fst p21 | Snd p11, Snd p21 ->
    prog_eqb p11 p21
  | Unit, Unit ->
    true
  | Let (v1, p11, body1), Let (v2, p21, body2) ->
    String.equal v1 v2
    && prog_eqb p11 p21
    && prog_eqb body1 body2
  | Var v1, Var v2 ->
    String.equal v1 v2
  | _, _ -> false

let rec pp_prog fmt = function
  | Bool b ->
    fprintf fmt "(Bool %b)" b
  | Int i ->
    fprintf fmt "(Int %i)" i
  | Add (p1, p2) ->
    fprintf fmt "@[<hv>(Add@;<1 2>%a@;<1 2>%a)@]" pp_prog p1 pp_prog p2
  | Lt (p1, p2) ->
    fprintf fmt "@[<hv>(Lt@;<1 2>%a@;<1 2>%a)@]" pp_prog p1 pp_prog p2
  | If (c, p1, p2) ->
    fprintf fmt "@[<hv>(If@;<1 2>%a@;<1 2>%a@;<1 2>%a)@]" pp_prog c pp_prog p1 pp_prog p2
  | Pair (p1, p2) ->
    fprintf fmt "@[<hv>(Pair@;<1 2>%a@;<1 2>%a)@]" pp_prog p1 pp_prog p2
  | Fst p1 ->
    fprintf fmt "@[<hv>(Fst@;<1 2>%a)@]" pp_prog p1
  | Snd p1 ->
    fprintf fmt "@[<hv>(Snd@;<1 2>%a)@]" pp_prog p1
  | Let (v, p1, body) ->
    fprintf fmt "@[<hv>let %s = %a in@;<1 0>%a@]" v pp_prog p1 pp_prog body
  | Var v ->
    fprintf fmt "(Var %S)" v
  | Unit ->
    fprintf fmt "Unit"

exception Type_error

(* type environment *)

module Tenv = struct

  type t = (string * typ) list

  let empty = []

  let add : string -> typ -> t -> t = fun v t tenv -> (v, t) :: tenv
  
  let search : string -> t -> typ option = List.assoc_opt

end

type tenv = Tenv.t

(* Type inference rules:

⊢ tenv, prog : typ  says program prog has type typ
                    under the type environment tenv
                    , tenv is omitted if unused

   tenv(v) = typ    says string v has type typ in
                    the type environment tenv

    tenv[v=typ]     denotes the new type environment
                    after associating variable v to
                    type typ in the type environment
                    tenv

        ----------------
        ⊢ Bool b : TBool

         --------------
         ⊢ Int i : TInt 

   ⊢ p1 : TInt    ⊢ p2 : TInt
   --------------------------
      ⊢ Add (p1, p2) : TInt

    ⊢ p1 : TInt    ⊢ p2 : TInt
    --------------------------
       ⊢ Lt (p1, p2) : TBool

 ⊢ c : TBool   ⊢ p1 : t   ⊢ p2 : t
 ---------------------------------
       ⊢ If (c, p1, p2) : t

        ⊢ p1 : t1   ⊢ p2 : t2
    -----------------------------
    ⊢ Pair (p1, p2) : TProd t1 t2

        ⊢ p1 : TProd t1 t2
        ------------------
          ⊢ Fst p1 : t1

        ⊢ p1 : TProd t1 t2
        ------------------
          ⊢ Snd p1 : t2

          --------------
          ⊢ Unit : TUnit

⊢ tenv, p1 : t1   ⊢ tenv[v=t1], body : tb
-----------------------------------------
     ⊢ tenv, Let (v, p1, body) : tb

            tenv(v) = t
         -----------------
         ⊢ tenv, Var v : t

*)

let rec infer ?(tenv=Tenv.empty) : prog -> typ = function
  | Bool _ -> TBool
  | Int _ -> TInt
  | Add (p1, p2) ->
    (match infer ~tenv p1, infer ~tenv p2 with
    | TInt, TInt -> TInt
    | _, _ -> raise Type_error)
  | Lt (p1, p2) ->
    (match infer ~tenv p1, infer ~tenv p2 with
    | TInt, TInt -> TBool
    | _, _ -> raise Type_error)
  | If (c, p1, p2) ->
    (match infer ~tenv c, infer ~tenv p1, infer ~tenv p2 with
    | TBool, t1, t2 when typ_eqb t1 t2 -> t1
    | _, _, _ -> raise Type_error)
  | Pair (p1, p2) ->
    TProd (infer ~tenv p1, infer ~tenv p2)
  | Fst p1 ->
    (match infer ~tenv p1 with
    | TProd (t1, _) -> t1
    | _ -> raise Type_error)
  | Snd p1 ->
    (match infer ~tenv p1 with
    | TProd (_, t2) -> t2
    | _ -> raise Type_error)
  | Unit ->
    TUnit
  | Let (v, p1, body) ->
    let tenv = Tenv.add v (infer ~tenv p1) tenv in
    infer ~tenv body
  | Var v ->
    (match Tenv.search v tenv with
    | Some t -> t
    | None -> raise Type_error)

let typable : prog -> bool = fun prog ->
  try let _ = infer prog in true
  with Type_error -> false

(* test the function infer and typable *)

(* true *)
let () = fprintf std_formatter "%b\n" (typable (If (Lt (Add (Int 1, Int 2), Int 3), Int 4, Int 5)))

(* false *)
let () = fprintf std_formatter "%b\n" (typable (Add (Int 1, Bool false)))

(* false *)
let () = fprintf std_formatter "%b\n" (typable (If (Bool true, Int 1, Bool false)))

(* (int * bool) *)
let () = fprintf std_formatter "%a\n" pp_typ (infer (Pair (Int 1, Bool false)))

(* the program that swaps the two elements of a pair is typable *)
let pair_swap = Let ("p", Pair (Int 1, Bool false), Pair (Snd (Var "p"), Fst (Var "p")))

(* (bool * int) *)
let () = fprintf std_formatter "%a\n" pp_typ (infer pair_swap)

(* Environment *)

module Env = struct

  type t = (string * prog) list

  let empty = []

  let add : string -> prog -> t -> t = fun v t tenv -> (v, t) :: tenv
  
  let search : string -> t -> prog option = List.assoc_opt
  
  let cancel : string -> t -> t = List.remove_assoc

end

type env = Env.t

(* Reduction rules:

  ⊢ env1, prog1 -> env2, prog2  says program prog1 under the environment env1
                                can be reduced to program prog2, modifying the
                                environment to env2, env is omitted if unused

          env(v) = prog         says variable v is mapped to program prog i
                                the environment env

           env[v=prog]          denotes the new environment after associating
                                variable v to program prog in the environment env

  -------------------------------------
  Add (Int i1, Int i2) -> Int (i1 + i2)

               p1 -> p1'
      -----------------------------
      Add (p1, p2) -> Add (p1', p2)

               p2 -> p2'
      -----------------------------
      Add (p1, p2) -> Add (p1, p2')

  --------------------------------------
  Lt (Int i1, Int i2) -> Bool (i1 <? i2)

              p1 -> p1'
      ---------------------------
      Lt (p1, p2) -> Lt (p1', p2)

              p2 -> p2'
      ---------------------------
      Lt (p1, p2) -> Lt (p1, p2')

      ----------------------------
      If (Bool true, p1, p2) -> p1

      -----------------------------
      If (Bool false, p1, p2) -> p2

                 c -> c'
    ---------------------------------
    If (c, p1, p2) -> If (c', p1, p2)

                p1 -> p1'
      -------------------------------
      Pair (p1, p2) -> Pair (p1', p2)

                p2 -> p2'
      -------------------------------
      Pair (p1, p2) -> Pair (p1, p2')

        -------------------------
        Fst (Pair (p1, p2)) -> p1

                p -> p'
            ---------------
            Fst p -> Fst p'

        -------------------------
        Snd (Pair (p1, p2)) -> p2

                p -> p'
            ---------------
            Snd p -> Snd p'

                p1 -> p1'
  ---------------------------------------
  Let (v, p1, body) -> Let (v, p1', body)

 -----------------------------------------
 env, Let (v, p1, body) -> env[v=p1], body

               env(v) = p
          --------------------
          env, Var v -> env, p

*)

let rec reduce_aux env prog : (env * prog) option =
  match prog with
  | Add (Int i1, Int i2) ->
    Some (env, Int (i1 + i2))
  | Add (p1, p2) ->
    (match reduce_aux env p1 with
    | Some (_, p1') ->
      Some (env, Add (p1', p2))
    | None ->
      (match reduce_aux env p2 with
      | Some (_, p2') ->
        Some (env, Add (p1, p2'))
      | None ->
        None) )
  | Lt (Int i1, Int i2) ->
    if i1 < i2
    then Some (env, Bool true)
    else Some (env, Bool false)
  | Lt (p1, p2) ->
    (match reduce_aux env p1 with
    | Some (_, p1') ->
      Some (env, Lt (p1', p2))
    | None ->
      (match reduce_aux env p2 with
      | Some (_, p2') ->
        Some (env, Lt (p1, p2'))
      | None ->
        None) )
  | If (Bool true, p1, _) ->
    Some (env, p1)
  | If (Bool false, _, p2) ->
    Some (env, p2)
  | If (c, p1, p2) ->
    (match reduce_aux env c with
    | Some (_, c') ->
      Some (env, If (c', p1, p2))
    | None ->
      None)
  | Pair (p1, p2) ->
    (match reduce_aux env p1 with
    | Some (_, p1') ->
      Some (env, Pair (p1', p2))
    | None ->
      (match reduce_aux env p2 with
      | Some (_, p2') ->
        Some (env, Pair (p1, p2'))
      | None ->
        None) )
  | Fst (Pair (p1, _)) ->
    Some (env, p1)
  | Fst p ->
    (match reduce_aux env p with
    | Some (_, p') ->
      Some (env, Fst p')
    | None ->
      None)
  | Snd (Pair (_, p2)) ->
    Some (env, p2)
  | Snd p ->
    (match reduce_aux env p with
    | Some (_, p') ->
      Some (env, Snd p')
    | None ->
      None)
  | Let (v, p, body) ->
    (match reduce_aux env p with
    | Some (_, p') ->
      Some (env, Let (v, p', body))
    | None ->
      Some (Env.add v p env, body) )
  | Var v ->
    (match Env.search v env with
    | Some p -> Some (env, p)
    | None -> None)
  | _ -> None

let reduce : prog -> prog option = fun prog ->
  match reduce_aux Env.empty prog with
  | Some (_, prog') -> Some prog'
  | None -> None

let rec normalize : prog -> prog = fun prog ->
  match reduce prog with
  | Some prog -> normalize prog
  | None -> prog

(* test the function normalize *)

(* Int 5 *)
let () = fprintf std_formatter "%a\n"
  pp_prog (normalize (If (Lt (Add (Int 1, Add (Int 2, Int 3)), Int 4), Bool false, Int 5)))

(* Parallel reduction rules:

              env[-v]                     denotes the environment with the variable v deleted

--------------------------------------
Add (Int i1, Int i2) -p> Int (i1 + i2)

        p1 -p> p1'   p2 -p> p2'
    -------------------------------
    Add (p1, p2) -p> Add (p1', p2')

---------------------------------------
Lt (Int i1, Int i2) -p> Bool (i1 <? i2)

        p1 -p> p1'   p2 -p> p2'
     -----------------------------
     Lt (p1, p2) -p> Lt (p1', p2')

              p1 -p> p1'
     ------------------------------
     If (Bool true, p1, p2) -p> p1'

              p2 -p> p2'
     -------------------------------
     If (Bool false, p1, p2) -p> p2'

   c -p> c'   p1 -p> p1'   p2 -p> p2'
  ------------------------------------
  If (c, p1, p2) -p> If (c', p1', p2')

        p1 -p> p1'   p2 -p> p2'
   ---------------------------------
   Pair (p1, p2) -p> Pair (p1', p2')

              p1 -p> p1'
      ---------------------------
      Fst (Pair (p1, p2)) -p> p1'

               p -p> p'
             ------------
             Fst p -p> p'

              p2 -p> p2'
      ---------------------------
      Snd (Pair (p1, p2)) -p> p2'

              p -p> p'
             ------------
             Snd p -p> p'

env, p1 -p> env, p1'   env, body -p> env, body'
-----------------------------------------------    ( body should be reduced under an environment without )
  env, Let (v, p1, body) -p> env[v=p1'], body'          the variable v, attention if v exists in env )

              env(v) = p
        ---------------------
        env, Var v -p> env, p

*)

let rec preduce_aux env prog : env * prog =
  match prog with
  | Add (Int i1, Int i2) ->
    env, Int (i1 + i2)
  | Add (p1, p2) ->
    let _, p1' = preduce_aux env p1 in
    let _, p2' = preduce_aux env p2 in
    env, Add (p1', p2')
  | Lt (Int i1, Int i2) ->
    env, Bool (i1 < i2)
  | Lt (p1, p2) ->
    let _, p1' = preduce_aux env p1 in
    let _, p2' = preduce_aux env p2 in
    env, Lt (p1', p2')
  | If (Bool true, p1, _) ->
    preduce_aux env p1
  | If (Bool false, _, p2) ->
    preduce_aux env p2
  | If (c, p1, p2) ->
    let _, c' = preduce_aux env c in
    let _, p1' = preduce_aux env p1 in
    let _, p2' = preduce_aux env p2 in
    env, If (c', p1', p2')
  | Pair (p1, p2) ->
    let _, p1' = preduce_aux env p1 in
    let _, p2' = preduce_aux env p2 in
    env, Pair (p1', p2')
  | Fst (Pair (p1, _)) ->
    let _, p1' = preduce_aux env p1 in
    env, p1'
  | Fst p ->
    let _, p' = preduce_aux env p in
    env, Fst p'
  | Snd (Pair (_, p2)) ->
    let _, p2' = preduce_aux env p2 in
    env, p2'
  | Snd p ->
    let _, p' = preduce_aux env p in
    env, Snd p'
  | Let (v, p, body) ->
    let _, p' = preduce_aux env p in
    let _, body' = preduce_aux (Env.cancel v env) body in
    Env.add v p' env, body'
  | Var v ->
    (match Env.search v env with
    | Some p -> env, p
    | None -> env, prog)
  | _ ->
    env, prog

let preduce : prog -> prog = fun prog ->
  snd (preduce_aux Env.empty prog)

let rec pnormalize : prog -> prog = fun prog ->
  let prog' = preduce prog in
  if prog_eqb prog prog' then prog
  else pnormalize prog'

(* test the function pnormalize *)

(* Bool false *)
let () = fprintf std_formatter "%a\n"
  pp_prog (pnormalize (If (Lt (Add (Int 1, Add (Int 2, Int 3)), Int 4), Bool false, Int 5)))


(* in order to implement functions:
    program:
      - add Let, LetRec, Func, App, Var
    type inference:
      - define type environment
      - introduce type variables when typing a (possibly recursive) function
      - build and unify type equations
    reduction:
      - define environment
      - define value in order to represent function closures
*)
