type var = string

type t =
  | Var of var
  | App of t * t
  | Abs of var * t

val id : t
val btrue : t
val bfalse : t
val bif : t
val nat : int -> t
val succ : t
val pred_fun : t
val pred : t
val add : t
val minus : t
val mul : t
val iszero : t
val pair : t
val fst : t
val snd : t
val fixpoint : t
val factorial : t

val abss : var list -> t -> t
val apps : t list -> t
