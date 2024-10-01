open Format

(* auxiliary functions *)

let map x f =
  match x with
  | Some x -> Some (f x)
  | None -> None

let ( let+ ) = map

let pp_option pp fmt = function
  | Some v -> fprintf fmt "Some (%a)" pp v
  | None -> fprintf fmt "None"

(* definitions *)

type nat =
  | Zero
  | Succ of nat
  
let rec pp_nat fmt = function
  | Zero ->
    fprintf fmt "Zero"
  | Succ Zero ->
    fprintf fmt "Succ Zero"
  | Succ n ->
    fprintf fmt "Succ (%a)" pp_nat n

let rec add : nat -> nat -> nat = fun x y ->
  match x, y with
  | Zero, y ->
    y
  | Succ x, y ->
    Succ (add x y)
  
let one = Succ Zero

let two = Succ one

let three = Succ two

let four = Succ three

let five = Succ four

(* test the function add *)

let () = fprintf std_formatter "%a\n" pp_nat (add two three)

let rec even : nat -> bool = function
  | Zero ->
    true
  | Succ Zero ->
    false
  | Succ (Succ n) ->
    even n

let pred : nat -> nat option = function
  | Zero ->
    None
  | Succ n ->
    Some n

let rec half : nat -> nat = function
  | Zero | Succ Zero ->
    Zero
  | Succ (Succ n) ->
    Succ (half n)

(* test the function half *)

let () = fprintf std_formatter "%a\n" pp_nat (half five)

let rec half_none_on_odd : nat -> nat option = function
  | Zero ->
    Some Zero
  | Succ Zero ->
    None
  | Succ (Succ n) ->
    let+ half_n = half_none_on_odd n in
    Succ half_n

(* test the function half_none_on_odd *)

let () = fprintf std_formatter "%a\n" (pp_option pp_nat) (half_none_on_odd five)

let () = fprintf std_formatter "%a\n" (pp_option pp_nat) (half_none_on_odd (add five five))
