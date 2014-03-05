module Martes where

{- Propositional logic in Agda -}

prop : Set₁
prop = Set

{- Proving some basic combinators. -}

I : {P : prop} → P → P
I = λ x → x

K : {P Q : prop} → P → Q → P
K = λ x x' → x

S : {P Q R : prop} → (P → Q → R) → (P → Q) → P → R
S = λ x x' x0 → x x0 (x' x0)

B : {P Q R : prop} → (P → Q) → (Q → R) → P → R
B = {!!}

C : {P Q R : prop} → (P → Q → R) → Q → P → R
C = {!!}

{- S, K are sufficent to prove all other tautologies involving only →. -}

I' : {P : prop} → P → P
I' {P} = S K (K {Q = P})

B' : {P Q R : prop} → (P → Q) → (Q → R) → P → R
B' = {!!}

C' : {P Q R : prop} → (P → Q → R) → Q → P → R
C' = {!!}

{- draw the truth table and then try to prove it -}

P : {P Q : prop} → ((P → Q) → P) → P
P = {!!}

{- Defining other connectives -}

data _∧_ (P Q : prop) : prop where
  _,_ : P → Q → P ∧ Q

infixr 2 _∧_

{- C-c C-, gives you the current "proof state" -}
∧-comm : {P Q : prop} → P ∧ Q → Q ∧ P
∧-comm (p , q) = q , p

data _∨_ (P Q : prop) : prop where
    left : P → P ∨ Q
    right : Q → P ∨ Q

distrib→ : {P Q R : prop} → P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)
distrib→ (y , left y') = left (y , y')
distrib→ (y , right y') = right (y , y')

distrib← : {P Q R : prop} → (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)
distrib← = {!!}

{- how do the two programs relate.
   there is more than just if and only iff.
 -}

_⇔_ : prop → prop → prop
P ⇔ Q = (P → Q) ∧ (Q → P)

infixr 0 _⇔_

distrib⇔ : {P Q R : prop} → P ∧ (Q ∨ R) ⇔ (P ∧ Q) ∨ (P ∧ R)
distrib⇔ = distrib→ , distrib←

curry→ : {P Q R : prop} → (P ∧ Q → R) → (P → Q → R)
curry→ = {!!}

curry← : {P Q R : prop} → (P → Q → R) → (P ∧ Q → R)
curry← = {!!}

curry⇔ : {P Q R : prop} → (P ∧ Q → R) ⇔ (P → Q → R)
curry⇔ = {!!}

∨∧→ : {P Q R : prop} → (P ∨ Q → R) → ((P → R) ∧ (Q → R))
∨∧→ = {!!}

∨∧← : {P Q R : prop} → ((P → R) ∧ (Q → R)) → (P ∨ Q → R) 
∨∧← = {!!}

∨∧ : {P Q R : prop} → (P ∨ Q → R) ⇔ ((P → R) ∧ (Q → R))
∨∧ = {!!}

{- a different equivalence -}

copy : {A : prop} → A ⇔ A ∧ A
copy = {!!}

{- some combinators -}

fst : {A B : prop} → A ∧ B → A
fst = {!!}

snd : {A B : prop} → A ∧ B → B
snd = {!!}

case : {A B C : prop} → (A → C) → (B → C) → A ∨ B → C
case = {!!}

or-com : {P Q : prop} → P ∨ Q → Q ∨ P
or-com = case right left

{- challenge: reprove distrib only with combinators. -}
distribC : {P Q R : prop} → P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)
distribC = {!!}

{- introduce true (⊤) and false (⊥) -}

{- \top = ⊤ -}
data ⊤ : prop where
  tt : ⊤

{- \bot = ⊥ -}
data ⊥ : prop where
{- this space is intentionally left blank. -}

efq : {P : prop} → ⊥ → P
efq ()

¬ : prop → prop
¬ P = P → ⊥

contradict : {P : prop} → ¬ (P ∧ ¬ P)
contradict (p , np) = np p

contrapos : {P Q : prop} → (P → Q) → ¬ Q → ¬ P
contrapos = {!!}

paradox : {P : prop} → ¬ (P ⇔ ¬ P) 
paradox = {!!}


{- Let's prove the de Morgan laws -}

deMorgan¬∨ : {P Q : prop} → ¬ (P ∨ Q) → ¬ P ∧ ¬ Q 
deMorgan¬∨ npq = (λ x → npq (left x)) , (λ x → npq (right x))
  
deMorgan¬∧¬ : {P Q : prop} → (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q)
deMorgan¬∧¬ = {!!}
  
deMorgan¬∨¬ : {P Q : prop} → (¬ P) ∨ (¬ Q) → ¬ (P ∧ Q)
deMorgan¬∨¬ = {!!}

deMorgan¬∧ : {P Q : prop} → ¬ (P ∧ Q) → (¬ P) ∨ (¬ Q)
deMorgan¬∧ npq = {!!}

{- on classical vs intuitionistic reasoning. -}

{-
tnd : {P : prop} → P ∨ ¬ P
tnd = {!!} -- not provable
-}

¬¬ : prop → prop
¬¬ P = ¬ (¬ P)

pnnp : {P : prop} → P → ¬¬ P 
pnnp p np = np p

{-
raa : {P : prop} → ¬¬ P → P
raa nnp = efq (nnp (λ x → nnp (λ x' → {!!})))
not provable, -}

¬¬tnd : {P : prop} → ¬¬ (P ∨ ¬ P)
¬¬tnd ¬P∨¬P = ¬P∨¬P (right (λ x → ¬P∨¬P (left x)))

TND : Set₁
TND = {P : prop} → P ∨ ¬ P

RAA : Set₁
RAA = {P : prop} → ¬¬ P → P

RAA→TND : RAA → TND
RAA→TND = {!!}

TND→RND : TND → RAA
TND→RND = {!!}

ret¬¬ : {P : prop} → P → ¬¬ P
ret¬¬ = {!!}

bind¬¬ : {P Q : prop} → ¬¬ P → (P → ¬¬ Q) → ¬¬ Q 
bind¬¬ = {!!}

map¬¬ : {P Q : prop} → ¬¬ P → (P → Q) → ¬¬ Q
map¬¬ = {!!}

app¬¬ : {P Q : prop} → ¬¬ (P → Q) → ¬¬ P → ¬¬ Q
app¬¬ = {!!}

∧¬¬-1 : {P Q : prop} → ¬¬ (P ∧ Q) → ¬¬ P ∧ ¬¬ Q
∧¬¬-1 = {!!}

∧¬¬-2 : {P Q : prop} → ¬¬ P ∧ ¬¬ Q → ¬¬ (P ∧ Q) 
∧¬¬-2 = {!!}

∧¬¬ : {P Q : prop} → ¬¬ (P ∧ Q) ⇔ ¬¬ P ∧ ¬¬ Q
∧¬¬ = {!!}

∨¬¬-1 : {P Q : prop} → ¬¬ (P ∨ Q) → ¬¬ P ∨ ¬¬ Q
∨¬¬-1 nnpq = {!!} 

∨¬¬-2 : {P Q : prop} → ¬¬ P ∨ ¬¬ Q → ¬¬ (P ∨ Q) 
∨¬¬-2 = {!!}

∨¬¬ : {P Q : prop} → ¬¬ (P ∨ Q) ⇔ ¬¬ P ∨ ¬¬ Q
∨¬¬ = {!!} 

¬¬deMorgan¬∧ : {P Q : prop} → ¬ (P ∧ Q) → ¬¬ ((¬ P) ∨ (¬ Q))
¬¬deMorgan¬∧ = {!!}

{- Predicate logic -}

{- If A : Set,
      P : A → prop
   then ∀ a : A, P a : prop
   is   (a : A) → P a
-}

∀∧ : {A : Set}{P Q : A → prop} → 
  ((a : A) → P a ∧ Q a) → ((a : A) → P a) ∧ ((a : A) → Q a)
∀∧ h = (λ a → fst (h a)) , (λ a → snd (h a))

∧∀ : {A : Set}{P Q : A → prop} → 
  ((a : A) → P a) ∧ ((a : A) → Q a) → ((a : A) → P a ∧ Q a)
∧∀ (y , y') = λ a → (y a) , (y' a)

∀∨ : {A : Set}{P Q : A → prop} → 
  ((a : A) → P a ∨ Q a) → ((a : A) → P a) ∨ ((a : A) → Q a)
∀∨ pq = {!!}

∨∀ : {A : Set}{P Q : A → prop} → 
  ((a : A) → P a) ∨ ((a : A) → Q a) → ((a : A) → P a ∨ Q a)
∨∀ = {!!}

{- Existential quantification: given a set A, and a predicate P : A → Prp
   ∃ A P : Prop means that P a is true (inhabited) for some a:A.
   A proof of this is a (depndent) pair (a , p) where a : A and 
   p : P a is a proof that P a is true (inhabited).
-}
data ∃ (A : Set)(P : A → prop) : prop where
  _,_ : (a : A) → P a → ∃ A P

∃∧ : {A : Set}{P Q : A → prop} → 
  (∃ A (λ a → P a ∧ Q a)) → (∃ A P) ∧ (∃ A Q)
∃∧ = {!!}

∧∃ : {A : Set}{P Q : A → prop} →
  (∃ A P) ∧ (∃ A Q) → (∃ A (λ a → P a ∧ Q a))
∧∃ x = {!!}

∃∨ : {A : Set}{P Q : A → prop} → 
  (∃ A (λ a → P a ∨ Q a)) → (∃ A P) ∨ (∃ A Q)
∃∨ (a , left y) = left (a , y)
∃∨ (a , right y) = right (a , y)

∨∃ : {A : Set}{P Q : A → prop} → 
  (∃ A P) ∨ (∃ A Q) → (∃ A (λ a → P a ∨ Q a))
∨∃ = {!!}

{- the infinite deMorgan rules - which ones are provable? -}

{- ¬ (∃ x:A. P x) ⇔ ∀ x:A. ¬ P x -}
deMorgan¬∃ : {A : Set}{P : A → prop} →
           ¬ (∃ A (λ x → P x)) → ((x : A) → ¬ (P x))
deMorgan¬∃ = {!!}

deMorgan∀¬ : {A : Set}{P : A → prop} →
           ((x : A) → ¬ (P x)) → ¬ (∃ A (λ x → P x))
deMorgan∀¬ = {!!}

{- ¬ (∀ x:A. P x) ⇔ ∃ x:A . ¬ P x -}
deMorgan¬∀ : {A : Set}{P : A → prop} →
             ¬ ((x : A) → P x) → ∃ A (λ x → ¬ (P x))
deMorgan¬∀ = {!!}

deMorgan∃¬ : {A : Set}{P : A → prop} →
           ∃ A (λ x → ¬ (P x)) → ¬ ((x : A) → P x)
deMorgan∃¬ = {!!}

{- relating ∀ and ∃ -}

curry∀→ : {A : Set}{P : A → Set}{Q : prop}
         → ((∃ A P) → Q) → (a : A) → P a → Q
curry∀→ x = {!!}

curry∀← : {A : Set}{P : A → Set}{Q : prop}
         → ((a : A) → P a → Q) → ((∃ A P) → Q)
curry∀← x = {!!}

{- the axiom of choice -}

{- ∀ a:A ∃ b:B . R a b → ∃ f : A → B . ∀ a:A . R a (f a) -}

fst' : {A : Set}{P : A → prop}
       → ∃ A P → A
fst' (a , y) = a

snd' : {A : Set}{P : A → prop}
       → (p : ∃ A P) → P (fst' p)
snd' (a , y) = y

ac : {A B : Set}{R : A → B → prop} → 
     ((a : A) → ∃ B λ b → R a b)
     → ∃ (A → B) λ f → (a : A) → R a (f a)
ac h = (λ x → fst' (h x)) , λ x → snd' (h x)

cac : {A B : Set}{R : A → B → prop} → 
     ((a : A) → ¬¬ (∃ B λ b → R a b))
     → ¬¬ (∃ (A → B) λ f → (a : A) → R a (f a))
cac h = {!!}

{- Cex : A = TM, B = Bool, R m b = true <-> m holds -}

dac : {A : Set}{B : A → Set}{R : (a : A) → B a → Set} 
      → ((a : A) → ∃ (B a) (λ b → R a b))
      → ∃ ((a : A) → B a) (λ f → (a : A) → R a (f a))
dac = {!!}