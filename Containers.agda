
open module Data.AVL.Sets

module Containers where

record Container : Sets where
               field
                 S : Set
                 P : S → Set

record Functor : Sets where
               field
                 obj : Set → Set
                 morp : (A , B : Set) → (A → B) → (obj A → obj B)

〚 _ 〛c : Container → Functor

record NatTrans (F , G : Functor) : Sets
               field
                 fam : (A : Set) → obj F A → obj G A 
                 nat : 
                   f : A → B

record _→c_ {A , B : Container } : Set where
               field
                 shape : Shape A → Shape B
                 position : ∀ {s} 