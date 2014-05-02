{-# OPTIONS --without-K #-}

module Multiset where
open import lib.Basics
open import lib.types.Nat
open import lib.PathOver
open import lib.NType2 

-- should be moved to a library module later
data Fin : ℕ → Type₀ where
  zf : {n : ℕ} → Fin (S n)
  sf : {n : ℕ} → Fin n → Fin (S n)

fin-is-set : (n : ℕ) → is-set (Fin n)
fin-is-set n = {!!}

module _ (n : ℕ) where

  private
    data #Sym : Type₀ where
      #* : #Sym

  #symrec : ∀ {i} (A : Type i) → A → #Sym → A
  #symrec A a _ = a

  Sym : Type₀
  Sym = #Sym

  * : Sym
  * = #*

  postulate -- HIT definition
    p : (Fin n ≃ Fin n) → * == *
    tr : (f₁ f₂ : Fin n ≃ Fin n) → p (f₂ ∘e f₁) == (p f₁) ∙ (p f₂)
    h : has-level (S ⟨0⟩) Sym 

module SymRec (n : ℕ)
              {i}
              (A : Type i)
              (base : A)
              (loops : (Fin n ≃ Fin n) → base == base)
              (comp-loops : (f₁ f₂ : Fin n ≃ Fin n) → loops (f₂ ∘e f₁) == (loops f₁) ∙ (loops f₂))
              (h : has-level (S ⟨0⟩) A)
                where
  rec : Sym n → A
  rec = #symrec n A base 

open SymRec public using () renaming (rec to sym-rec)
  
{-
Now, we have defined a type 
  Sym n
that corresponds to the symmetric group on the n element set.
It is the "shape" type of the construction.
Its recursor is called sym-rec. We did not define the eliminator
(it is hopefully not needed).
-}

-- define Positions:
module _ (n : ℕ) where

  P-aux : Sym n → hSet lzero
  P-aux = sym-rec n {lsucc lzero} (hSet lzero) (Fin n , fin-is-set _) paths p-trans hSet-is-grp where

    paths : Fin n ≃ Fin n → (Fin n , fin-is-set n) == (Fin n , fin-is-set n)
    paths e = pair= pathaux pathaux'  where 

      pathaux : Fin n == Fin n
      pathaux = ua e

      pathaux': PathOver (λ A → is-set A) interesting (fin-is-set n) (fin-is-set n)
      pathaux' = (from-transp is-set interesting (prop-has-all-paths is-set-is-prop _ _)) 

    p-trans :  (f₁ f₂ : Fin n ≃ Fin n) → paths (f₂ ∘e f₁) == paths f₁ ∙ paths f₂
    p-trans = {!!}

    hSet-is-grp : has-level _ (hSet _)
    hSet-is-grp = hSet-level _


  P : Sym n → Type lzero
  P = fst ∘ P-aux
  

{-
 module test (n : ℕ) where

  data Sym : Set where
    * : Sym
-}


    
    