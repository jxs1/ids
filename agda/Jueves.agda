module Jueves where

open import Data.Nat hiding (_≤_ ; module _≤_ ; _≤?_ ; _<_)
open import Relation.Binary.PropositionalEquality -- defines ≡ 
open import Relation.Nullary
open import Data.String


data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n}                 → zero  ≤ n
  s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n

{- examples -}

2≤4 : 2 ≤ 4
2≤4 = s≤s (s≤s z≤n)


¬4≤2 : ¬ 4 ≤ 2
¬4≤2 (s≤s (s≤s ()))

{- We want to show that ≤ is a partial order, i.e. it is reflexive,
   transitive and antisymmetric. -}  

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s (≤-refl {n})

≤-trans : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
≤-trans z≤n q = z≤n
≤-trans (s≤s m≤n) (s≤s m≤n') = s≤s (≤-trans m≤n m≤n')

≤-asym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-asym = {!!}

≤-unique : {m n : ℕ} → (p q : m ≤ n) → p ≡ q
≤-unique = {!!}

{- Finally we establish that ≤ is decidable: -}


_≤?_ : (m n : ℕ) → Dec (m ≤ n)
_≤?_ = {!!}

{- an alternative definition of ≤ -}

data _≤'_ : ℕ → ℕ → Set where
  n≤'n : ∀ {n}                 → n  ≤' n
  m≤'s : ∀ {m n} (m≤n : m ≤' n) → m ≤' suc n

m≤s : ∀ {m n} (m≤n : m ≤ n) → m ≤ suc n
m≤s z≤n = z≤n
m≤s (s≤s m≤n) = s≤s (m≤s m≤n)

≤'→≤ : ∀ {m}{n} → m ≤' n → m ≤ n
≤'→≤ n≤'n = ≤-refl
≤'→≤ (m≤'s m≤n) = m≤s (≤'→≤ m≤n)

≤→≤' : ∀ {m}{n} → m ≤ n → m ≤' n
≤→≤' = {!!}

{- A simpler example: Even -}

data Even : ℕ → Set where
  zero : Even zero
  sucsuc : ∀ {n} → Even n → Even (suc (suc n))

{- show that 4 is even. -}

even4 : Even 4
even4 = {!!}
{- show that 3 is not even. -}

¬even3 : ¬ (Even 3)
¬even3 = {!!}

{- show that sucsuc is invertible -}

inv-sucsuc : ∀ {n} → Even (suc (suc n)) → Even n 
inv-sucsuc  = {!!}

{- show that there is at most one proof of even. -}

even-unique : ∀ {m} → (p q : Even m) → p ≡ q
even-unique = {!!}

{- show that even is decidable. -}

even? : (n : ℕ) → Dec (Even n)
even? = {!!}

{- Combinatoric logic: minimal propositional logic -}

data Formula : Set where
  Atom : String → Formula
  _⇒_ : (A B : Formula) → Formula

infixr 6 _⇒_ 

{- Here is an example formula - the translation of (P -> Q) -> P -}
example : Formula
example = ((Atom "P") ⇒ (Atom "Q")) ⇒ Atom "P"

data Context : Set where
  ε : Context
  _·_ : (Γ : Context) → (A : Formula) → Context

infix 4 _⊢sk_
infix 4 _⊢_
infixl 5 _·_

data _⊢_ : Context → Formula → Set where
  ass : ∀ {Γ A} → Γ · A ⊢ A
  weak : ∀ {Γ A B} → Γ ⊢ A → Γ · B ⊢ A
  app : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  abs : ∀ {Γ A B} → Γ · A ⊢ B → Γ ⊢ A ⇒ B

I : ∀ {Γ}{A} → Γ ⊢ A ⇒ A
I = abs ass  

{- In combinatory logic we add three combinators pair, fst and snd -}

data _⊢sk_ : Context → Formula → Set where
  ass : ∀ {Γ A} → Γ · A ⊢sk A
  weak : ∀ {Γ A B} → Γ ⊢sk A → Γ · B ⊢sk A
  app : ∀ {Γ A B} → Γ ⊢sk A ⇒ B → Γ ⊢sk A → Γ ⊢sk B
  K : ∀ {Γ A B} → Γ ⊢sk A ⇒ B ⇒ A
  S : ∀ {Γ A B C} → Γ ⊢sk (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C

K' : ∀ {Γ A B} → Γ ⊢ A ⇒ B ⇒ A
K' = abs (abs (weak ass))

S' : ∀ {Γ A B C} → Γ ⊢ (A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C
S' = {!!}

⊢sk→⊢ : ∀ {Γ A} → Γ ⊢sk A → Γ ⊢ A
⊢sk→⊢ ass = ass
⊢sk→⊢ (weak y) = weak (⊢sk→⊢ y)
⊢sk→⊢ (app y y') = app (⊢sk→⊢ y) (⊢sk→⊢ y')
⊢sk→⊢ K = K'
⊢sk→⊢ S = S'

I' : ∀ {Γ}{A} → Γ ⊢sk A ⇒ A
I' {A = A} = app (app S K) (K {B = A})

abs' : ∀ {Γ A B} → Γ · A ⊢sk B → Γ ⊢sk A ⇒ B
abs' ass = I'
abs' (weak y) = app K y
abs' (app y y') = app (app S (abs' y)) (abs' y')
abs' K = app K K
abs' S = app K S

⊢→⊢sk : ∀ {Γ A} → Γ ⊢ A → Γ ⊢sk A
⊢→⊢sk ass = ass
⊢→⊢sk (weak y) = weak (⊢→⊢sk y)
⊢→⊢sk (app y y') = app (⊢→⊢sk y) (⊢→⊢sk y')
⊢→⊢sk (abs y) = {!!}

{- apply the translation to the problems from Tuesday. -}

{- Extend to conjunction and disjunction by adding:

  _∨_ :  (A B : Formula) → Formula
  _∧_ :  (A B : Formula) → Formula

  pair : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
  elim : ∀ {Γ A B C} → Γ · A · B ⊢ C → Γ · A ∧ B ⊢ C
  left : ∀ {Γ A B} → Γ ⊢ A → Γ ⊢ A ∨ B
  right : ∀ {Γ A B} → Γ ⊢ B → Γ ⊢ A ∨ B
  case : ∀ {Γ A B C} → Γ · A ⊢ C → Γ · B ⊢ C → Γ · A ∨ B ⊢ 

  pair : ∀ {Γ A B} → Γ ⊢sk A ⇒ B ⇒ A ∧ B
  fst : ∀ {Γ A B} → Γ ⊢sk A ∧ B ⇒ A
  snd : ∀ {Γ A B} → Γ ⊢sk A ∧ B ⇒ B
  left : ∀ {Γ A B} → Γ ⊢sk A ⇒ A ∨ B
  right : ∀ {Γ A B} → Γ ⊢sk B ⇒ A ∨ B
  case : ∀ {Γ A B C} → Γ ⊢sk (A ⇒ C) ⇒ (B ⇒ C) ⇒ A ∨ B ⇒ C

infixl 7 _∧_
infixl 7 _∨_
-}

{- Use this to solve the exercise from Tuesday! -}

{- challenge: reprove distrib only with combinators. -}

{-
distribC : {P Q R : prop} → P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)
distribC = {!!}
-}
