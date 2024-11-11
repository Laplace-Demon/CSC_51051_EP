open import Data.Product

×-comm : {A B : Set} → (A × B) → (B × A)
×-comm (fst , snd) = (snd , fst)

id : {A : Set} → A → A
id a = a

K : {A B : Set} → A → B → A
K a b = a

app : {A B : Set} → (A → B) → A → B
app f a = f a

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b

comp : {A B C : Set} → (A → B) → (B → C) → (A → C)
comp f g a = g (f a)

S : {A B C : Set} → (A → B → C) → (A → B) → A → C
S f g a = f a (g a)

open import Data.Product renaming (_×_ to _∧_)

proj1 : {A B : Set} → A ∧ B → A
proj1 (a , b) = a

proj2 : {A B : Set} → A ∧ B → B
proj2 (a , b) = b

diag : {A : Set} → A → A ∧ A
diag a = (a , a)

∧-comm : {A B : Set} → A ∧ B → B ∧ A
∧-comm = ×-comm

curry1 : {A B C : Set} → (A ∧ B → C) → (A → B → C)
curry1 f a b = f (a , b)

curry2 : {A B C : Set} → (A → B → C) → (A ∧ B → C)
curry2 f (a , b) = f a b

equiv : (A B : Set) → Set
equiv A B = (A → B) ∧ (B → A)

_↔_ : (A B : Set) → Set
_↔_ A B = (A → B) ∧ (B → A)

currying : {A B C : Set} → (A ∧ B → C) ↔ (A → B → C)
currying = (curry1 , curry2)

→distrib : {A B C : Set} → (A → (B ∧ C)) ↔ ((A → B) ∧ (A → C))
→distrib = (λ f → (λ a → proj1 (f a)) , (λ a → proj2 (f a))) , (λ f a → ((proj1 f) a) , ((proj2 f) a))

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

or-elim : {A B C : Set} → (A ∨ B) → (A → C) → (B → C) → C
or-elim (left a) f g  = f a
or-elim (right b) f g = g b

or-comm : (A B : Set) → (A ∨ B) → (B ∨ A)
or-comm A B (left a) = right a
or-comm A B (right b) = left b

dist : {A B C : Set} → (A ∧ (B ∨ C)) → (A ∧ B) ∨ (A ∧ C)
dist (a , left b) = left (a , b)
dist (a , right c) = right (a , c)

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

¬ : Set → Set
¬ = λ x → x → ⊥

contr : {A B : Set} → (A → B) → (¬ B → ¬ A)
contr f not-b a = ⊥-elim (not-b (f a))

non-contr : {A : Set} → ¬ (A ∧ ¬ A)
non-contr (a , not-a) = not-a a

nni : {A : Set} → A → ¬ (¬ A)
nni a f = f a

⊥-nne : ¬ (¬ ⊥) → ⊥
⊥-nne not-not-false = not-not-false id

¬-elim : {A B : Set} → ¬ A → A → B
¬-elim not-a a = ⊥-elim (not-a a)

dm∧ : {A B : Set} → ¬ A ∧ ¬ B → ¬ (A ∨ B)
dm∧ (not-a , not-b) (left a)  = not-a a
dm∧ (not-a , not-b) (right b) = not-b b

dm∨ : {A B : Set} → ¬ A ∨ ¬ B → ¬ (A ∧ B)
dm∨ (left not-a) (a , b) = not-a a
dm∨ (right not-b) (a , b) = not-b b

dm∧-converse : {A B : Set} → ¬ (A ∨ B) → ¬ A ∧ ¬ B
dm∧-converse not = (λ a → not (left a)) , (λ b → not (right b))

-- We cannot prove dm∨-converse without the law of excluded middle 

nnlem : {A : Set} → ¬ (¬ (A ∨ (¬ A)))
nnlem not with (nnlem-helper not)
  where
  nnlem-helper : {A : Set} → ¬ (A ∨ ¬ A) → ¬ A ∧ ¬ (¬ A)
  nnlem-helper or = (λ a → or (left a)) , λ not-a → or (right not-a)
nnlem not | not-a , not-not-a = not-not-a not-a

rp : {A : Set} → (A → ¬ A) → ((¬ A) → A) → ⊥
rp f g =
  let
    a = g (λ a → f a a)
  in
  f a a

data ⊤ : Set where
  tt : ⊤

ti : {A : Set} → (⊤ → A) → A
ti f = f tt

dmnt : ¬ ⊤ → ⊥
dmnt = ti

dmtn : ⊥ → ¬ ⊤
dmtn = K

lem : Set₁
lem = (A : Set) → A ∨ (¬ A)

nne : Set₁
nne = (A : Set) → ¬ (¬ A) → A

nne-lem : nne → lem
nne-lem nne = λ A → nne (A ∨ (¬ A)) nnlem

lem-nne : lem → nne
lem-nne lem A not-not-a with lem A
lem-nne lem A not-not-a | left a = a
lem-nne lem A not-not-a | right not-a = ⊥-elim (not-not-a not-a)

-- Here, A and B are put in parenthesis (instead of curly braces) to keep a consistent style

pierce : Set₁
pierce = (A B : Set) → ((A → B) → A) → A

lem-pierce : lem → pierce
lem-pierce lem A B impl with lem A
lem-pierce lem A B impl | left a = a
lem-pierce lem A B impl | right not-a = impl λ a → ⊥-elim (not-a a)

pierce-nne : pierce → nne
pierce-nne pierce A not-not-a = pierce A ⊥ λ not-a → ⊥-elim (not-not-a not-a)

postulate U : Set

∀-comm : {P : U → U → Set} → ((x : U) → (y : U) → P x y) → ((y : U) → (x : U) → P x y)
∀-comm f y x = f x y

∃-comm : {P : U → U → Set} → ∃ (λ x → ∃ (λ y → P x y)) → ∃ (λ y → ∃ (λ x → P x y))
∃-comm (x , y , P) = (y , x , P)

∃-∀-change : {P : U → U → Set} → ∃ (λ x → (y : U) → P x y) → ((y : U) → ∃ (λ x → P x y))
∃-∀-change (x , forall-y) = λ y → (x , forall-y y)

lemma₁ : {P Q : U → Set} → ((x : U) → P x) ∨ ((x : U) → Q x) → ((x : U) → P x ∨ Q x)
lemma₁ (left Px) = λ x → left (Px x)
lemma₁ (right Qx) = λ x → right (Qx x)

lemma₂ : {P Q : U → Set} → equiv ((x : U) → P x ∧ Q x) (((x : U) → P x) ∧ ((x : U) → Q x))
lemma₂ = (λ P-and-Q → (λ x → proj1 (P-and-Q x)) , (λ x → proj2 (P-and-Q x)))
       , (λ (Px , Qx) x → (Px x) , (Qx x))

lemma₃ : {P : U → Set} → ∃ (λ x → ¬ (P x)) → ¬ ((x : U) → P x)
lemma₃ (x , not-Px) = λ Px → not-Px (Px x)

lemma₄ : {P : U → Set} → ((x : U) → ¬ (P x)) → ¬ (∃ (λ x → P x))
lemma₄ not-Px (x , Px) = (not-Px x) Px
