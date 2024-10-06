open Format

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
  let z = Var 2 in
  let z' = Not z in
  let a = And (And (Or (x, y), Or (x', y)), Or (x', y')) in
  let b = And (And (Or (x, y), Or (x', y)), And (Or (x, y'), Or (x', y'))) in
  let c = And (x, And (y, (And (z, x')))) in
  assert (sat a);
  assert (not (sat b));
  assert (not (sat c))

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
    if f x then x :: (list_filter f l) else list_filter f l
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

let () =
  assert (list_concat [ [ 1 ] ; [] ; [ 2 ; 3 ; 4 ] ; [ 5 ; 6 ] ] = [ 1 ; 2 ; 3 ; 4 ; 5 ; 6 ])

let rec subst_cnf : var -> bool -> cnf -> cnf = fun v b -> function
  | c :: cnf' ->
    if list_mem (b, v) c
    then subst_cnf v b cnf'
    else list_filter (fun (b', v') -> b = b' || v != v') c :: subst_cnf v b cnf'
  | [] ->
    []

let () =
  let c1 = [ (true, 0) ; (false, 1) ; (true, 2) ] in
  let c2 = [ (true, 0) ; (true, 1) ; (false, 2) ] in
  assert (subst_cnf 1 true [ c1 ; c2 ] = [ [ (true, 0) ; (true, 2) ] ])

let rec dpll : cnf -> bool = fun cnf ->
  match cnf with
  | [] ->
    true
  | [] :: _ ->
    false
  | ((b, v) :: _) :: _ ->
    dpll (subst_cnf v b cnf) || dpll (subst_cnf v (not b) cnf)

let () =
  let x = true, 0 in
  let x'= false,0 in
  let y = true, 1 in
  let y'= false,1 in
  let a = [[x;y]; [x';y]; [x';y']] in
  let b = [[x;y]; [x';y]; [x;y']; [x';y']] in
  assert (dpll a);
  assert (not (dpll b))

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

let pure : cnf -> literal = fun cnf ->
  let literals = list_concat cnf in
  match list_filter (fun (b, v) -> not (list_mem (not b, v) literals)) literals with
  | l :: _ ->
    l
  | _ ->
    raise Not_found

let () =
  let x = (true, 0) in
  let x' = (false, 0) in
  let y = (true, 1) in
  let y' = (false, 1) in
  let z = (true, 2) in
  let z' = (false, 2) in
  assert (pure [ [ x ; y ; z ; z' ] ; [ x ; y' ; z ] ; [ x ; y ; y' ; z ; z' ] ] = (true, 0))

let rec dpll : cnf -> bool = fun cnf ->
  match cnf with
  | [] ->
    true
  | [] :: _ ->
    false
  | c :: _ ->
  try
    let (b, v) = unit cnf in
    dpll (subst_cnf v b cnf)
  with | Not_found ->
  try
    let (b, v) = pure cnf in
    dpll (subst_cnf v b cnf)
  with | Not_found ->
    let (b, v) = List.hd c in
    dpll (subst_cnf v b cnf) || dpll (subst_cnf v (not b) cnf)

let () =
  let x = true, 0 in
  let x'= false,0 in
  let y = true, 1 in
  let y'= false,1 in
  let a = [[x;y]; [x';y]; [x';y']] in
  let b = [[x;y]; [x';y]; [x;y']; [x';y']] in
  assert (dpll a);
  assert (not (dpll b))

let mom : cnf -> var = fun cnf ->
  let cnf = List.sort (fun c1 c2 -> Int.compare (List.length c1) (List.length c2)) cnf in
  match cnf with
  | c :: _ ->
    let min_len = List.length c in
    let clauses = list_filter (fun c' -> Int.equal min_len (List.length c')) cnf in
    let literals = list_map (fun (_, v) -> v) (list_concat clauses) in
    let occur_list = List.fold_left
      (fun occ var ->
        match List.assoc_opt var occ with
        | Some cnt -> list_map (fun (var', cnt') -> if Int.equal var var' then (var', cnt' + 1) else (var', cnt')) occ
        | None -> (var, 1) :: occ) [] literals in
    (match List.rev (List.sort (fun (_, x) (_, y) -> Int.compare x y) occur_list) with
    | (v, _) :: _ -> v
    | [] -> raise Not_found)
  | [] -> raise Not_found

let () =
  let c1 = [ (true, 0) ; (false, 1) ] in
  let c2 = [ (true, 0) ; (false, 2) ] in
  let c3 = [ (true, 1) ; (true, 1) ; (false, 2) ] in
  let c4 = [ (true, 1) ; (true, 2) ; (false, 2) ] in
  assert (mom [ c1 ; c2 ; c3 ; c4 ] = 0)

let rec dpll : cnf -> bool = fun cnf ->
  match cnf with
  | [] ->
    true
  | [] :: _ ->
    false
  | c :: _ ->
  try
    let (b, v) = unit cnf in
    dpll (subst_cnf v b cnf)
  with | Not_found ->
  try
    let (b, v) = pure cnf in
    dpll (subst_cnf v b cnf)
  with | Not_found ->
  try
    let v = mom cnf in
    dpll (subst_cnf v true cnf) || dpll (subst_cnf v false cnf)
  with | Not_found ->
    let (_, v) = List.hd c in
    dpll (subst_cnf v true cnf) || dpll (subst_cnf v false cnf)

let () =
  let x = true, 0 in
  let x'= false,0 in
  let y = true, 1 in
  let y'= false,1 in
  let a = [[x;y]; [x';y]; [x';y']] in
  let b = [[x;y]; [x';y]; [x;y']; [x';y']] in
  assert (dpll a);
  assert (not (dpll b))

let jw : cnf -> literal -> float = fun cnf literal ->
  List.fold_left Float.add 0.
    (list_map (fun clause -> if list_mem literal clause then
      Float.pow 0.5 (Float.of_int (List.length clause)) else 0.) cnf)

let jw_var : cnf -> var = fun cnf ->
  let literals = List.sort_uniq (fun l1 l2 -> compare l1 l2) (list_concat cnf) in
  let ranks = List.sort (fun (r1, _) (r2, _) -> Float.compare r1 r2)
    (list_map (fun l -> (jw cnf l, snd l)) literals) in
  match List.rev ranks with
  | (_, v) :: _ -> v
  | [] -> raise Not_found

let () =
  let c1 = [ (true, 0) ; (false, 1) ] in
  let c2 = [ (true, 0) ; (false, 2) ] in
  let c3 = [ (true, 1) ; (true, 1) ; (false, 1) ] in
  let c4 = [ (true, 1) ; (true, 2) ; (false, 2) ] in
  assert (jw_var [ c1 ; c2 ; c3 ; c4 ] = 0)

let rec dpll : cnf -> bool = fun cnf ->
  match cnf with
  | [] ->
    true
  | [] :: _ ->
    false
  | c :: _ ->
  try
    let (b, v) = unit cnf in
    dpll (subst_cnf v b cnf)
  with | Not_found ->
  try
    let (b, v) = pure cnf in
    dpll (subst_cnf v b cnf)
  with | Not_found ->
  try
    let v = jw_var cnf in
    dpll (subst_cnf v true cnf) || dpll (subst_cnf v false cnf)
  with | Not_found ->
    let (_, v) = List.hd c in
    dpll (subst_cnf v true cnf) || dpll (subst_cnf v false cnf)

let () =
  let x = true, 0 in
  let x'= false,0 in
  let y = true, 1 in
  let y'= false,1 in
  let a = [[x;y]; [x';y]; [x';y']] in
  let b = [[x;y]; [x';y]; [x;y']; [x';y']] in
  assert (dpll a);
  assert (not (dpll b))

(** Parse a CNF file. *)
let parse f : cnf =
  let load_file f =
    let ic = open_in f in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Bytes.to_string s
  in
  let f = load_file f in
  let f = String.map (function '\t' -> ' ' | c -> c) f in
  let f = String.split_on_char '\n' f in
  let f = List.map (String.split_on_char ' ') f in
  let f = List.filter (function "c"::_ | "p"::_ -> false | _ -> true) f in
  let f = List.flatten f in
  let aux (a,c) = function
    | "" -> (a,c)
    | "0" -> (c::a,[])
    | n ->
       let n = int_of_string n in
       let x = if n < 0 then (false,-n) else (true,n) in
       (a,x::c)
  in
  fst (List.fold_left aux ([],[]) f)

(* testing the dpll implementation *)

(* takes one minute *)
(* let () = assert (dpll (parse "cnf/ais12.cnf"))
let () = assert (dpll (parse "cnf/flat50-1000.cnf"))
let () = assert (dpll (parse "cnf/ii8a2.cnf"))
let () = assert (dpll (parse "cnf/quinn.cnf"))
let () = assert (dpll (parse "cnf/zebra_v155_c1135.cnf")) *)

(* takes unknown number of minutes *)
(* let () = assert (not (dpll (parse "cnf/aim-50-1_6-no-1.cnf")))
let () = assert (not (dpll (parse "cnf/bf1355-075.cnf")))
let () = assert (not (dpll (parse "cnf/dubois20.cnf")))
let () = assert (not (dpll (parse "cnf/dubois21.cnf")))
let () = assert (not (dpll (parse "cnf/hole6.cnf"))) *)

(*
  Var (var i j n) whether the cell (i, j) has value n + 1

  Conditions:
  
    there is at least one number in each cell
      
      And_{i, j} (Or_{n} (Var (var i j n)))
      
    each number occurs at most once in a row
    
      And_{i, n} (And_{j1, j2} (Or (Not (Var (var i j1 n)), Not (Var (i j2 n)))))
    
    each number occurs at most once in a column
    
      And_{j, n} (And_{i1, i2} (Or (Not (Var (var i1 j n)), Not (Var (i2 j n)))))

    each number occurs at most once in a square
    
      And_{square, n} (And_{i1, j1, i2, j2 in the square} (Or (Not (Var (var i1 j1 n)), Not (Var (var i2 j2 n)))))

    the solution respects the game given in argument
    
      And_{i, j such that array[i][j] != 9} (Var (var i j array[i][j]))
*)

let var i j n : var =
  9 * (9 * i + j) + n

let sudoku : int array array -> cnf = fun a ->
  let range = List.init 9 (fun n -> n) in
  let line_combination =
    let temp = ref [] in
    for i = 0 to 8 do
      for j = i + 1 to 8 do
        temp := (i, j) :: !temp
      done
    done; !temp
  in
  let square = List.init 9 (fun n -> ((n / 3) * 3, (n mod 3) * 3)) in
  let square_combination =
    let temp = ref [] in
    let offset = Array.init 9 (fun n -> (n / 3, n mod 3)) in
    for i = 0 to 8 do
      for j = i + 1 to 8 do
        temp := (offset.(i), offset.(j)) :: !temp
      done
    done; !temp
  in
  let cond1 =
    list_concat (list_map (fun i ->
      list_map (fun j ->
        list_map (fun n ->
          (true, var i j n))
          range) range) range)
  in
  let cond2 =
    list_concat (list_map (fun i ->
      list_concat (list_map (fun n ->
        list_map (fun (j1, j2) ->
          [ (false, var i j1 n) ; (false, var i j2 n) ])
          line_combination) range)) range)
  in
  let cond3 =
    list_concat (list_map (fun j ->
      list_concat (list_map (fun n ->
        list_map (fun (i1, i2) ->
          [ (false, var i1 j n) ; (false, var i2 j n) ])
          line_combination) range)) range)
  in
  let cond4 =
    list_concat (list_map (fun n ->
      list_concat (list_map (fun (i, j) ->
        list_map (fun ((i1, j1), (i2, j2)) ->
          [ (false, var (i + i1) (j + j1) n) ; (false, var (i + i2) (j + j2) n)])
          square_combination) square)) range)
  in
  let cond5 =
    list_concat (List.mapi (fun i line ->
       list_filter (fun l -> l <> []) (List.mapi (fun j n ->
        if n = 9 then [] else [ (true, var i j n) ])
        (Array.to_list line))) (Array.to_list a))
  in
  cond1 @ cond2 @ cond3 @ cond4 @ cond5
  
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

(* takes several seconds *)
let () =
  assert (dpll (sudoku simple_sudoku))

let () =
  assert (dpll (sudoku medium_sudoku))

let () =
  assert (dpll (sudoku hard_sudoku))

(* takes unknown number of seconds *)
(* let () =
  assert (not (dpll (sudoku unsolvable_sudoku))) *)
  
(* rendering in CNF *)

let rec cnf_aux : bool -> formula -> cnf = fun b -> function
  | Var v ->
    [ [ b, v ] ]
  | And (f1, f2) ->
    if b
    then
      let cnf1 = cnf_aux true f1 in
      let cnf2 = cnf_aux true f2 in
      cnf1 @ cnf2
    else
      let cnf1 = cnf_aux false f1 in
      let cnf2 = cnf_aux false f2 in
      list_concat (list_map (fun c1 -> list_map (fun c2 -> c1 @ c2) cnf2) cnf1)
  | Or (f1, f2) ->
    if b
    then
      let cnf1 = cnf_aux true f1 in
      let cnf2 = cnf_aux true f2 in
      list_concat (list_map (fun c1 -> list_map (fun c2 -> c1 @ c2) cnf2) cnf1)
    else
      let cnf1 = cnf_aux false f1 in
      let cnf2 = cnf_aux false f2 in
      cnf1 @ cnf2
  | Not f ->
    cnf_aux (not b) f
  | True ->
    if b
    then []
    else [ [] ]
  | False ->
    if b
    then [ [] ]
    else []

let cnf = cnf_aux true
