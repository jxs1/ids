
module Containers where

record Functor : Sets where
               field
                 obj : Set → Set
                 morp : (A,B : Set) → (A → B) → (obj A → obj B)

record Container : Sets where
                 field
                   S : Set
                   P : S → Set