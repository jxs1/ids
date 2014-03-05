module Miercoles where

{- Basic constructions in Type Theory -}

{- Π - types -}

{- built in : (x : A) → B -}

{- Σ - types -}

open import Data.Product

{- ⊎ = \uplus -}
{- disjoint union (⊎) -}

open import Data.Sum

{- Equality -}

open import Relation.Binary.PropositionalEquality hiding (sym ; trans ; cong ; subst )

{- Using pattern matching we can prove that ≡ is symmetric & transitive
   and hence an equivalence relation (because refl proves reflexivity)/ -}

sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl q = q

{- Any function respects equality: -}

cong : {A B : Set}(f : A → B){a b : A} → a ≡ b → f a ≡ f b
cong f refl = refl

{-
cong' : {A B : Set}(f : A → B){a b : A} →  f a ≡ f b → a ≡ b
cong' f p = {!p!}
-}

subst : {A : Set}(P : A → Set) → {a b : A} → a ≡ b → P a → P b
subst P refl x = x

{- Derive sym and trans using subst -}

sym' : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym' = {!!}

trans' : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans' = {!!}

{- uniqueness of identity proofs -}

uip : {A : Set}{a b : A}(p q : a ≡ b) → p ≡ q
uip refl refl = refl

{- Induction and recursion -}

open import Data.Nat 

0+ : (n : ℕ) → zero + n ≡ n
0+ n = refl

+0 : (n : ℕ) → n + zero ≡ n
+0 zero = refl
+0 (suc n) = cong suc (+0 n)

{- Let's look at the interaction of + and suc -}

+suc : (m n : ℕ) → m + (suc n) ≡ suc (m + n)
+suc = {!!}

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero n = {!!}
+-comm (suc n) n' = {!!}

{- nicer way to write proofs -}

open ≡-Reasoning
open import Data.Product

+-comm' : (m n : ℕ) → m + n ≡ n + m
+-comm' m zero = +0 m 
+-comm' m (suc n) = begin 
            m + suc n   ≡⟨ +suc m n ⟩
            suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
            suc n + m  ∎

{- some more proofs about arithmetic (ℕ,0,+,1,*) is a comm. semiring. -}

+-assoc : (i j k : ℕ) → (i + j) + k ≡ i + (j + k)
+-assoc = {!!}

*-comm : (m n : ℕ) → m * n ≡ n * m
*-comm = {!!}

{- induction and recursion -}

{- All the constructions using ℕ can be reduced to a basic combinator: -}

ℕelim : (P : ℕ → Set) → 
      P zero → 
      ((n : ℕ) → P n → P (suc n)) → 
      (n : ℕ) → P n
ℕelim P z s zero = z
ℕelim P z s (suc n) = s n (ℕelim P z s n)

ℕrec : (A : Set) → A → (ℕ → A → A) → ℕ → A
ℕrec A = ℕelim (λ _ → A)

{- derive + * using ℕRec -}
_+R_ : ℕ → ℕ → ℕ
_+R_ = {!!}

_*R_ : ℕ → ℕ → ℕ
_*R_ = {!!}

{- Reprove +0' using ℕElim -}

+0' : (n : ℕ) → n + zero ≡ n
+0' = {!!}

{- 
  Decidabililty 

  Equality on natural numbers is decidable, i.e. we can implement a
  boolean function which returns true if two numbers are equal, and
  false otherwise.
-}

open import Data.Bool 

_≡b_ : ℕ → ℕ → Bool
zero ≡b zero = true
zero ≡b suc n = false
suc n ≡b zero = false
suc n ≡b suc m = n ≡b m

{- implement ≡b just using ℕrec -}

_≡bR_ : ℕ → ℕ → Bool
_≡bR_ = {!!}

open import Relation.Nullary 

{- We prove that ≡ is "decidable", i.e. for every m,n : ℕ we can 
   decide m ≡ n.
-}

lem : (n : ℕ) → ¬ (0 ≡ suc n)
lem n ()

_≡?_ : (m n : ℕ) → Dec (m ≡ n)
zero ≡? zero = yes refl
zero ≡? suc n = no (λ ())
suc n ≡? zero = no (λ ())
suc n ≡? suc n' with n ≡? n'
suc .n' ≡? suc n' | yes refl = yes refl
suc n ≡? suc n' | no ¬p = no (λ x → ¬p (cong pred x))

-- 3 ≡? 3
-- 3 ≡? 4

{- The similarity with ≡b should be obvious. The difference is that ≡?
   doesn't just say "yes" or "no" corresponding to "true" and "false"
   but it also provides the evidence why it is ok to give this answer.

   Also we should note that ≡? is at the same time a program and a proof. 
-}

{- another example decidability for the equality of binary trees -}

data BT : Set where
  leaf : BT
  node : BT → BT → BT

_≡BT?_ : (m n : BT) → Dec (m ≡ n)
t ≡BT? t' = {!!}

{- Example : mod₂ -}

{- Define functions,
   mod₂ : remainder of division by 2
   div₂ : division by two 
-}
mod₂ : ℕ → ℕ 
mod₂ = {!!}

div₂ : ℕ → ℕ
div₂ = {!!}

{- And prove the following properties: -}

mod₂Lem : (n : ℕ) → mod₂ n ≡ 0 ⊎ mod₂ n ≡ 1
mod₂Lem = {!!}

div₂Lem : ∀ {n} → 2 * (div₂ n) + mod₂ n ≡ n
div₂Lem = {!!}

{- Show that equality modulo 2 is decidable. -}

_≡₂_ : ℕ → ℕ → Set
m ≡₂ n = mod₂ m ≡ mod₂ n

_≡₂?_ : (m n : ℕ) → Dec (m ≡₂ n)
_≡₂?_ = {!!}

{- additional exercise: do it for mod (n+1) -}