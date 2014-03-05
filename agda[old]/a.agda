module a where

data Bool : Set where
  T : Bool
  F : Bool

!_ : Bool → Bool
! T = F
! F = T

if_then_else_ : {A : Set} → Bool → A → A → A
if T then x else y = x
if F then x else y = y

data ℕ : Set where
  o : ℕ
  succ : ℕ → ℕ

add : ℕ → ℕ → ℕ
add o y = y
add (succ y) y' = succ (add y y')

_+_ : ℕ → ℕ → ℕ
o + y = y
succ y + y' = succ (y + y')

one = succ o
two = one + one

data List (A : Set) : Set where
  Nil : List A
  Cons : A → List A → List A

length : {A : Set} → List A → ℕ
length Nil = o
length (Cons y y') = succ (length y')

map : {A B : Set} → (A → B) → List A → List B
map f Nil = Nil
map f (Cons y y') = Cons (f y) (map f y')

concat : {A : Set} → List A → List A → List A
concat Nil y = y
concat (Cons y y') y0 = Cons y (concat y' y0)

--implicit type and also value parameters

data Vector (A : Set) : ℕ → Set where
  ε : Vector A o
  V : {n : ℕ} → A → Vector A n → Vector A (succ n)

vLength : {A : Set} → {n : ℕ} → Vector A n → ℕ
vLength {_} {n} v = n

vMap : {A B : Set} → {n : ℕ} → (A → B) → Vector A n → Vector B n
vMap f ε = ε
vMap f (V y y') = V (f y) (vMap f y')

----------------------------------------------------

