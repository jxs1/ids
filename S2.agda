module jon2 where

open import Relation.Binary.PropositionalEquality

dcong : {A : Set}(B : A → Set)(f : (x : A) → B x){a a' : A}(p : a ≡ a') → subst B p (f a) ≡ f a'
dcong B f refl = refl

{-
data S¹ : Set where
  base : S¹
  loop : base ≡ base
-}
module Sphere where

  private data S¹aux : Set where
               base : S¹aux

  S¹ : Set
  S¹ = S¹aux

  postulate loop : base ≡ base

  RS¹ : (X : Set)(b : X)(l : b ≡ b) → S¹ → X
  RS¹ X b l base = b

  postulate RS¹l :  (X : Set)(b : X)(l : b ≡ b) → cong (RS¹ X b l) loop ≡ l

  ES¹ : (X : S¹ → Set)(b : X base)(l : subst X loop b ≡ b)(x : S¹) → X x
  ES¹ X b l base = b

  postulate ES¹l : (X : S¹ → Set)(b : X base)(l : subst X loop b ≡ b) → dcong X (ES¹ X b l) loop ≡ l

{-
unique : (x : S¹) → x ≡ base
unique = ES¹ (λ x → x ≡ base) refl {!!}
-}

open Sphere

unique : (x : S¹) → x ≡ base
unique base = refl