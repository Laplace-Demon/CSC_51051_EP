type var = int

type formula = 
  | Var of var
  | And of formula * formula
  | Or of formula * formula
  | Not of formula
  | True
  | False

(* subst v s f = f[s/v] *)
let rec subst (v : var) (s : formula) : formula -> formula = function
  | Var v' when v = v' ->
    s
  | And (f1, f2) ->
    And (subst v s f1, subst v s f2)
  | Or (f1, f2) ->
    Or (subst v s f1, subst v s f2)
  | Not f ->
    Not (subst v s f)
  | _ as f ->
    f

let rec free_vars : formula -> var list = function
  | Var v ->
    [v]
  | And (f1, f2) ->
    free_vars f1 @ free_vars f2
  | Or (f1, f2) ->
    free_vars f1 @ free_vars f2
  | Not f ->
    free_vars f
  | _ ->
    []

let free_var : formula -> var option = fun f ->
  List.nth_opt (free_vars f) 0
  
exception Not_closed_formula of formula

let rec eval : formula -> bool = function
  | Var _ as f ->
    raise (Not_closed_formula f)
  | And (f1, f2) ->
    eval f1 && eval f2
  | Or (f1, f2) ->
    eval f1 || eval f2
  | Not f ->
    not (eval f)
  | True ->
    true
  | False ->
    false

let rec sat : formula -> bool = fun f ->
  match free_var f with
  | Some v ->
    sat (subst v True f) || sat (subst v False f)
  | None ->
    eval f

let () =
  let x = Var 0 in
  let x'= Not x in
  let y = Var 1 in
  let y'= Not y in
  let a = And (And (Or (x, y), Or (x', y)), Or (x', y')) in
  let b = And (And (Or (x, y), Or (x', y)), And (Or (x, y'), Or (x', y'))) in
  assert (sat a);
  assert (not (sat b))

(* DPLL *)

type literal = bool * var
type clause = literal list
type cnf = clause list

let rec list_mem : 'a -> 'a list -> bool = fun x -> function
  | x' :: l ->
    if x = x' then true else list_mem x l
  | [] ->
    false

let () =
  assert (list_mem 2 [ 1 ; 2 ; 3 ]);
  assert (not (list_mem 5 [ 1 ; 2 ; 3 ]));
  assert (not (list_mem 1 []))

let rec list_map : ('a -> 'b) -> 'a list -> 'b list = fun f -> function
  | x :: l ->
    f x :: (list_map f l)
  | [] ->
    []

let () =
  assert (list_map (fun x -> 2 * x) [ 1 ; 2 ; 3 ] = [ 2 ; 4 ; 6 ]);
  assert (list_map (fun _ -> ()) [] = [])

let rec list_filter : ('a -> bool) -> 'a list -> 'a list = fun f -> function
  | x :: l ->
    if f x then list_filter f l else x :: (list_filter f l)
  | [] ->
    []

let () =
  let even x = x mod 2 = 0 in
  assert (list_filter even [ 1 ; 2 ; 3 ; 4 ; 6 ] = [ 2 ; 4 ; 6 ])

let rec list_concat : 'a list list -> 'a list = function
  | l :: ll ->
    l @ (list_concat ll)
  | [] ->
    []

let rec subst_cnf : var -> bool -> cnf -> cnf = fun v b -> function
  | c :: cnf' ->
    if list_mem (b, v) c
    then subst_cnf v b cnf'
    else list_filter (fun (b', v') -> b = b' || v = v') c :: subst_cnf v b cnf'
  | [] ->
    []

(* we cannot guarantee that the input cnf formula does not contain empty clauses *)
let rec dpll : cnf -> bool = function
  | (((b, v) :: _) :: _) as cnf ->
    begin
      match subst_cnf v b cnf with
      | [] ->
        true
      | _ as cnf ->
        dpll cnf
    end
  | [] :: _ ->
    false
  | [] ->
    true

let rec unit : cnf -> literal = function
  | [ l ] :: _ ->
    l
  | _ :: cnf ->
    unit cnf
  | [] ->
    raise Not_found

let () =
  let x = true, 0 in
  let y = true, 1 in
  let y' = false, 1 in
  assert (unit [ [ x ; y ] ; [ x ] ; [ y ; y' ] ] = x)

(*
  Var (var i j n) whether the cell (i, j) has value n

  Conditions:
  
    there is at least one number in each cell
      forall i j, exists n, Var (var i j n) = true
    
    each number occurs at most once in a row
      forall i n,

*)

let var i j n : var =
  9 * (9 * i + j) + n

let sodoku : int array array -> cnf =
  
  
(* testing the function sodoku *)

let simple_sudoku =
  [|[|9;9;7;9;8;2;4;9;9|];
    [|5;4;9;3;9;1;9;9;9|];
    [|9;1;0;9;7;9;2;9;9|];
    [|2;7;9;9;5;9;1;9;8|];
    [|9;6;9;9;9;9;9;0;9|];
    [|0;9;8;9;3;9;9;6;2|];
    [|9;9;4;9;0;9;6;2;9|];
    [|9;9;9;2;9;8;9;1;5|];
    [|9;9;5;7;1;9;0;9;9|]|]

let medium_sudoku =
  [|[|9;1;9;7;4;3;9;9;9|];
    [|9;9;9;5;9;9;9;9;7|];
    [|9;0;9;9;9;9;9;9;8|];
    [|1;9;9;9;9;9;9;8;2|];
    [|9;6;4;2;9;7;5;1;9|];
    [|7;8;9;9;9;9;9;9;6|];
    [|3;9;9;9;9;9;9;5;9|];
    [|2;9;9;9;9;1;9;9;9|];
    [|9;9;9;6;5;0;9;3;9|]|]
  
let hard_sudoku =
  [|[|9;9;9;9;4;9;8;9;9|];
    [|8;7;9;9;9;9;9;4;9|];
    [|9;3;4;6;9;9;2;9;9|];
    [|9;9;3;1;9;9;7;6;9|];
    [|9;9;9;0;9;3;9;9;9|];
    [|9;6;5;9;9;8;0;9;9|];
    [|9;9;7;9;9;0;5;2;9|];
    [|9;1;9;9;9;9;9;7;0|];
    [|9;9;6;9;2;9;9;9;9|]|]

let unsolvable_sudoku =
  [|[|1;9;9;8;9;9;9;9;9|];
    [|9;9;9;9;9;9;9;5;9|];
    [|9;9;9;9;9;0;9;9;9|];
    [|4;9;1;5;9;9;3;9;6|];
    [|9;9;9;9;9;3;0;9;9|];
    [|9;9;9;9;8;7;9;1;2|];
    [|9;9;9;9;9;2;9;7;9|];
    [|9;9;4;9;0;9;9;9;9|];
    [|9;9;6;9;9;9;9;9;9|]|]

let () =
  assert (dpll (sudoku simple_sudoku))

let () =
  assert (dpll (sudoku medium_sudoku))

let () =
  assert (dpll (sudoku hard_sudoku))

let () =
  assert (not (dpll (sudoku unsolvable_sudoku)))
  
(* rendering in CNF *)

let rec cnf_aux : bool -> formula -> cnf = fun b -> function
  | Var v ->
    [ [ b, v ] ]
  | And (f1, f2) ->
    if b
    then
      let cnf1 = cnf_aux b f1 in
      let cnf2 = cnf_aux b f2 in
      cnf1 @ cnf2
    else
      let cnf1 = cnf_aux (not b) f1 in
      let cnf2 = cnf_aux (not b) f2 in
      list_concat (list_map (fun c1 -> list_map (fun c2 -> c1 @ c2) cnf2) cnf1)
  | Or (f1, f2) ->
    if b
    then
      let cnf1 = cnf_aux b f1 in
      let cnf2 = cnf_aux b f2 in
      list_concat (list_map (fun c1 -> list_map (fun c2 -> c1 @ c2) cnf2) cnf1)
    else
      let cnf1 = cnf_aux (not b) f1 in
      let cnf2 = cnf_aux (not b) f2 in
      cnf1 @ cnf2
  | Not f ->
    cnf_aux (not b) f
  | True ->
    []
  | False ->
    [ [] ]

let cnf = cnf_aux true
