{-# OPTIONS --without-K #-}

module Multiset where

open import lib/Basics
open import Data.Nat
open import Relation.Binary.HeterogeneousEquality.cong
open import Univalence

  Inductive S (n : ℕ)
    * : S n
    P : (Fin n ≅ Fin n) → * = *
    tr : (f₁, f₂ : Fin n ≅ Fin n) → p (f₂ ∘ f₁) = p f₁ ∘ p f₂
    h : is-1-type(S n)

    Pn : Sn → Type of 0-Types
    Pn(*) = Fin n
    Pn(p(f)) = univalence f


    
    