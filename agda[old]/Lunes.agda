module Lunes where

{-
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{- C-c C-l runs the type checker. -}
{- ℕ = \bn, → = \to -}

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)
{- C-c C-c splits cases -}
{- C-c C-r refines the problem -}
-}

open import Data.Nat
{- look up using M-click -}
open import Data.Bool

{- evaluate using C-c C-n -}

{- Write a function to decide equality of natural numbers,
   eq m n = true, if m=n
   eq m n = false, otherwise
-}
eq : ℕ → ℕ → Bool
eq m n = {!!}

open import Data.List

snoc : {A : Set} → List A → A → List A
snoc [] a = a ∷ []
snoc {A} (x ∷ xs) a = x ∷ snoc {A} xs a
{- C-c SPC to type check what I have written. -}

{- {A : Set} .. is an implicit parameter, it is inserted by the
   compiler. -}

rev : {A : Set} → List A → List A
rev as = {!!}

data ⊥ : Set where

open import Data.Maybe

{- return nth element of a list. -}
_!!_ : {A : Set} → List A → ℕ → Maybe A
xs !! n = {!!}
-- write the function with three lines!

open import Data.Vec

snoc' : {A : Set}{n : ℕ} → Vec A n → A → Vec A (suc n)
snoc' [] a = a ∷ []
snoc' (x ∷ xs) a = x ∷ (snoc' xs a)

rev' : {A : Set}{n : ℕ} → Vec A n → Vec A n
rev' as = {!!}

open import Data.Fin

enum : (n : ℕ) → Vec (Fin n) n
enum zero = []
enum (suc n) = zero ∷ Data.Vec.map suc (enum n)

max : {n : ℕ} → Fin (suc n)
max {zero} = zero {0}
max {suc n} = suc (max {n})

emb : {n : ℕ} → Fin n → Fin (suc n)
emb zero = zero
emb (suc i) = suc (emb i)

inv : {n : ℕ} → Fin n → Fin n
inv i = {!!}

_!!'_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
[] !!' () -- impossible pattern
(x ∷ xs) !!' zero = x
(x ∷ xs) !!' suc i = xs !!' i

{- Es imposible hacer trampa en Agda. -}

Vector : ℕ → Set {- Vec n is an n-dimensional vector -}
Vector m = Vec ℕ m

Matrix : ℕ → ℕ → Set {- Matrix m n is an m x n Matrix -}
Matrix m n = Vec (Vector n) m

{- multiplication with a scalar -}
_*v_ : {n : ℕ} → ℕ → Vector n → Vector n
k *v ms = {!!}

v1 : Vector 3
v1 = 1 ∷ 2 ∷ 3 ∷ []

test1 : Vector 3
test1 = 2 *v v1

{- addition of vectors -}
_+v_ : {n : ℕ} → Vector n → Vector n → Vector n
ms +v ns = {!!}

v2 : Vector 3
v2 = 2 ∷ 3 ∷ 0 ∷ []

test2 : Vector 3
test2 = v1 +v v2

{- multiplication of a vector and a matrix -}
_*vm_ : {m n : ℕ} → Vector m → Matrix m n → Vector n
ms *vm nss = {!!}

id3 : Matrix 3 3
id3 = (1 ∷ 0 ∷ 0 ∷ []) 
    ∷ (0 ∷ 1 ∷ 0 ∷ []) 
    ∷ (0 ∷ 0 ∷ 1 ∷ []) 
    ∷ []

test3 : Vector 3
test3 = v1 *vm id3

{- matrix multiplication -}
_*mm_ : {l m n : ℕ} → Matrix l m → Matrix m n → Matrix l n
mss *mm nss = {!!}

inv3 : Matrix 3 3
inv3 = (0 ∷ 0 ∷ 1 ∷ []) 
     ∷ (0 ∷ 1 ∷ 0 ∷ []) 
     ∷ (1 ∷ 0 ∷ 0 ∷ []) 
     ∷ []

test4 : Matrix 3 3
test4 = inv3 *mm inv3