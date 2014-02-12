module Viernes where 

open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

{- an untyped language of expressions -}

infix 3 _≤E_
infix 4 _+E_

data Expr : Set where
  nat : ℕ → Expr
  bool : Bool → Expr
  _+E_ : Expr → Expr → Expr
  _≤E_ : Expr → Expr → Expr
  ifE_then_else_ : Expr → Expr → Expr → Expr
  
{- Examples of expressions: -}

e1 : Expr -- if 3 ≤ 4 then 4 + 1 else 0
e1 = ifE (nat 3) ≤E (nat 4) then (nat 4) +E (nat 1) else (nat 0)

e2 : Expr -- 3 ≤ 4 + 5
e2 = (nat 3) ≤E (nat 4) +E (nat 5)

e3 : Expr -- (3 ≤ 4) + 5
e3 = ((nat 3) ≤E (nat 4)) +E (nat 5)

{- The result of evaluating an expression is a value -}

data Val : Set where
  nat : ℕ → Val
  bool : Bool → Val

{- To accomodate errors we introduce the Maybe monad.
   A Monad M is an operation on Sets such that M A is the type of
   computations over A. In the case of Maybe a computation is
   something that may go wrong (i.e. returns nothing).

   Each monad comes with two functions:

   return : {A : Set} → A → M A
   turns a value into a (trivial) computation.

   _>>=_ : {A B : Set} → M A → (A → M B) → M B
   (bind) m >>= f runs first the computation m and if it returns a
   value runs f in it. The effects are a combination of running both
   computations.
-}

open import Category.Monad
import Level
open RawMonad {f = Level.zero} monad

{-
-- for Maybe return is just (no error)
return : {A : Set} → A → Maybe A
return a = just a

infix 2 _>>=_

-- bind does error propagation
_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a >>= f = f a
nothing >>= f = nothing
-}

{- To implement the evaluator we implement some convenience
   functions. -}

{- Addition of two values has to check wether the values are indeed
   numbers -}
_+v_ : Val → Val → Maybe Val
nat m +v nat n = return (nat (m + n))
_ +v _ = nothing

{- dec2bool coerces decidability into bool by forgetting the
   evidence. -}
dec2bool : {A : Set} → Dec A → Bool
dec2bool (yes p) = true
dec2bool (no ¬p) = false

{- This is used to implement ≤ for values. As +v this has to check
   wether the arguments are numbers. -}
_≤v_ : Val → Val → Maybe Val
nat m ≤v nat n = return (bool (dec2bool (m ≤? n)))
_ ≤v _ = nothing

{- if-then-else for values. May return an error if the first argument
   is not a boolean.
-}
ifV_then_else_ : Val → Val → Val → Maybe Val
ifV bool b then v else v' = return (if b then v else v')
ifV _ then _ else _ = nothing

{- The evaluator. We use Scott-brackets (⟦ = \[[, ⟧ = \]]) as it is
   tradition to mark the borderline between syntax and semantics.
   Evlauation an expression may return a value of fail. -}
⟦_⟧ : Expr → Maybe Val
⟦ nat n ⟧ = return (nat n)
⟦ bool b ⟧ = return (bool b)
⟦ e +E e' ⟧ = ⟦ e ⟧ >>= λ v → 
             ⟦ e' ⟧ >>= λ v' →
             v +v v'
{- In Haskell we would use "do" syntax:
   do v <- ⟦ e ⟧
      v' <- ⟦ e' ⟧
      v +v v' 
-}
⟦ e ≤E e' ⟧ = ⟦ e ⟧ >>= λ v → 
             ⟦ e' ⟧ >>= λ v' →
             v ≤v v'
⟦ ifE e then e' else e'' ⟧ = ⟦ e ⟧ >>= λ v → 
                            ⟦ e' ⟧ >>= λ v' →
                            ⟦ e'' ⟧ >>= λ v'' →
                            ifV v then v' else v''


{- Evaluation the examples: -}

v1 : Maybe Val -- just (nat 5)
v1 = ⟦ e1 ⟧

v2 : Maybe Val -- just (bool true)
v2 = ⟦ e2 ⟧

v3 : Maybe Val
v3 = ⟦ e3 ⟧ -- nothing

{- We do everything again but this time for a typed language. -}

{- the types -}
data Ty : Set where
  nat : Ty
  bool : Ty

{- typed values -}
data TVal : Ty → Set where
  nat : ℕ → TVal nat
  bool : Bool → TVal bool

{- typed expressions -}
data TExpr : Ty → Set where
  nat : ℕ → TExpr nat
  bool : Bool → TExpr bool
  _+E_ : TExpr nat → TExpr nat → TExpr nat
  _≤E_ : TExpr nat → TExpr nat → TExpr bool
  ifE_then_else_ : {σ : Ty} → TExpr bool → TExpr σ → TExpr σ → TExpr σ

{- the typed evaluator
   doesn't need to use the Maybe monad because it will never fail. -}
⟦_⟧T : {σ : Ty} → TExpr σ → TVal σ
⟦ nat n ⟧T = nat n
⟦ bool b ⟧T = bool b
⟦ e +E e' ⟧T with ⟦ e ⟧T | ⟦ e' ⟧T
...         | nat m | nat n = nat (m + n)
⟦ e ≤E e' ⟧T with ⟦ e ⟧T | ⟦ e' ⟧T
...             | nat m | nat n = bool (dec2bool (m ≤? n))
⟦ ifE e then e' else e'' ⟧T with ⟦ e ⟧T 
...                           | bool b = if b then ⟦ e' ⟧T else ⟦ e'' ⟧T 

{- But what to do if just have got an untyped expression (maybe read
   from a file)? We use a type checker to lift an untyped expression
   to an equivalent typed expression (or fail).
-}


{- A forgetful map from typed expressions to untyped expressions -}
⌊_⌋ : {σ : Ty} → TExpr σ → Expr
⌊ nat n ⌋ = nat n
⌊ bool b ⌋ = bool b
⌊ e +E e' ⌋ = ⌊ e ⌋ +E ⌊ e' ⌋
⌊ e ≤E e' ⌋ = ⌊ e ⌋ ≤E ⌊ e' ⌋
⌊ ifE e then e' else e'' ⌋ =  ifE ⌊ e ⌋ then ⌊ e' ⌋ else ⌊ e'' ⌋

{- equality of types is clearly decidable -}
_≡Ty?_ : (σ τ : Ty) → Dec (σ ≡ τ)
nat ≡Ty? nat = yes refl
nat ≡Ty? bool = no (λ ())
bool ≡Ty? nat = no (λ ())
bool ≡Ty? bool = yes refl

{- The result of checking an expression e is a record containing: -}
record Check (e : Expr) : Set where
  constructor check
  field 
    σ : Ty                -- a type
    te : TExpr σ          -- a typed expression
    te≡e : ⌊ te ⌋ ≡ e    -- if we forget the types we recover e

{- This is the first time we use records in Agda.
   Look up the reference manual for a decription of records in Agda. -}

open Check
{- Records also use modules which hide the projection functions. By
   opening it we have direct access to the projection functions
   corresponding to the field names.
   E.g. we have 
   σ : Check e → Ty
   te : (c : Check e) → TExpr (σ c)
-}

{- We implement type inference by recursion over the expression. -}
infer : (e : Expr) → Maybe (Check e)
infer (nat n) = just (check nat (nat n) refl)
infer (bool b) = just (check bool (bool b) refl)
{- To infer a type for e + e' we recursively infer types for e and e'
(which may fail) and make sure that there are nat in which case we
return a typed expression of type nat. -}
infer (e +E e') with infer e | infer e'
infer (.(⌊ te ⌋) +E .(⌊ te' ⌋)) | just (check nat te refl) | just (check nat te' refl) 
      = just (check nat (te +E te') refl)
infer (e +E e') | _ |  _ = nothing
{- ≤ uses the same technique -}
infer (e ≤E e') with infer e | infer e'
infer (.(⌊ te ⌋) ≤E .(⌊ te' ⌋)) | just (check nat te refl) | just (check nat te' refl) 
      = just (check bool (te ≤E te') refl)
infer (e ≤E e') | _ |  _ = nothing
{- if-then-else also has to make sure that both branches have the same
   type, which is the type of the result. -}
infer (ifE e then e' else e'') with infer e | infer e' | infer e''
infer (ifE .(⌊ te ⌋) then .(⌊ te' ⌋) else .(⌊ te'' ⌋))  
      | just (check bool te refl) | just (check σ te' refl) | just (check σ' te'' refl) with σ ≡Ty? σ'
infer (ifE .(⌊ te ⌋) then .(⌊ te' ⌋) else .(⌊ te'' ⌋))  
      | just (check bool te refl) | just (check σ te' refl) | just (check .σ te'' refl)    | yes refl 
      = just (check σ (ifE te then te' else te'') refl)
infer (ifE .(⌊ te ⌋) then .(⌊ te' ⌋) else .(⌊ te'' ⌋))  
      | just (check bool te refl) | just (check σ te' refl) | just (check σ' te'' refl)    | no _     = nothing
infer (ifE e then e' else e'') | _ | _ | _ = nothing

{- A safe evaluator -}

{- We can also forget the types of typed values -}
⌊_⌋v : {σ : Ty} → TVal σ → Val
⌊ nat n ⌋v = nat n
⌊ bool b ⌋v = bool b

{- We implement a safe evaluator which has the same type as the
   untyped evaluator. It exploits the type checker to first produce a
   typed expression (or fail) and then runs the fast and safe typed
   evaluator. 
-}
⟦_⟧s : Expr → Maybe Val
⟦ e ⟧s = infer e >>= λ c → return (⌊ ⟦ Check.te c ⟧T ⌋v) 

{- For our examples that safe evaluator produces the same results: -}

v1' : Maybe Val
v1' = ⟦ e1 ⟧s

v2' : Maybe Val
v2' = ⟦ e2 ⟧s

v3' : Maybe Val
v3' = ⟦ e3 ⟧s

{- Is this always the case ? -}

data Code : Set where
  push : Val → Code → Code  -- push a value on the stack
  +M : Code → Code          -- add the top values on the stack
  ≤M : Code → Code          -- compare top values on the stack
  branch : Code → Code → Code -- branch depending on the top value
                              -- instead of gotos the code is tree-structured
  stop : Code -- end of computation

{- the set of stacks - basically a list of values.
   However, I prefer to write stacks backward - that is why I am not
   using stacks. -}
infixl 4 _▹_

data Stack : Set where
  ε : Stack
  _▹_ : Stack → Val → Stack

{- run executes the code, returning the final stack when the
   computation is finished. Note that we are using the partiality
   monad and the operations +v and ≤v from the last lecture which
   check wether their arguments have the right type. 
   Apart from dynamic type errors, run may also fail because there are
   not enough values on the stack.
-}
run : Stack → Code → Maybe Stack
run s (push v p) = run (s ▹ v) p
run ((s ▹ v) ▹ v') (+M p) = v +v v' >>= λ v+v' → run (s ▹ v+v') p
run _ (+M _) = nothing
run ((s ▹ v) ▹ v') (≤M p) = v ≤v v' >>= λ v≤v' → run (s ▹ v≤v') p
run _ (≤M _) = nothing
run (s ▹ bool true) (branch p p') = run s p
run (s ▹ bool false) (branch p p') = run s p'
run (s ▹ _) (branch _ _) = nothing
run _ (branch _ _) = nothing
run s stop = just s

{- The compiler is straightforward. We are using "continuation-passing
   style", i.e. the compiler gets the code which is to be exceuted
   after the translation of the expression. This has the advantage
   that we don't have to concatenate code (and hence is more
   efficient) and it is also easier to reason about (even though we
   are not going to prove compiler correctness now. -}
compile : Expr → Code → Code
compile (nat n) c = push (nat n) c
compile (bool b) c = push (bool b) c
compile (e +E e') c = compile e (compile e' (+M c))
  -- here we exploit the continuation passing style.
  -- to compile the who expression we first compile e then e' then add +M
compile (e ≤E e') c = compile e (compile e' (≤M c))
compile (ifE e then e' else e'') c = 
        compile e (branch (compile e' c) (compile e'' c))

{- combining compile and run. compiler correctness would be to show 
   that compileRun is extensionally equal to ⟦_⟧,i.e.

   correct : (e : Expr) compileRun e ≡ ⟦ e ⟧
-}
compileRun : Expr → Maybe Val
compileRun e with run ε (compile e stop)
...             | just (_ ▹ v) = just v
...             | _ = nothing

{- Instead of proving we just test our test cases. -}

v1'' : Maybe Val
v1'' = compileRun e1

v2'' : Maybe Val
v2'' = compileRun e2

v3'' : Maybe Val
v3'' = compileRun e3

{- Next we define "typed assembly language". The type of assembly code
   refers to the type of the stack before and after executing the
   code. -}

{- Stack types are just sequences of value types (defined in the
   previous lecture. -}
data StackTy : Set where
    ε : StackTy
    _▹_ : StackTy → Ty → StackTy

{- Typed stacks are indexed over stack types. -}
data TStack : StackTy → Set where
  ε : TStack ε
  _▹_ : ∀ {Γ σ} → TStack Γ → TVal σ → TStack (Γ ▹ σ)

{- Typed code is indexed by two stacks: the stack it expects and the
   stack after executing it. -}
data TCode : StackTy → StackTy → Set where
  push : ∀ {Γ Δ σ} → TVal σ → TCode (Δ ▹ σ)  Γ → TCode Δ Γ
  +M : ∀ {Γ Δ} → TCode (Δ ▹ nat) Γ → TCode (Δ ▹ nat ▹ nat) Γ
  ≤M : ∀ {Γ Δ} → TCode (Δ ▹ bool) Γ → TCode (Δ ▹ nat ▹ nat) Γ
  branch : ∀ {Γ Δ} → TCode Δ Γ → TCode Δ Γ → TCode (Δ ▹ bool) Γ
  stop : ∀ {Γ} → TCode Γ Γ

{- the typed machine doesn't need to use the Maybe monad becuase the 
   typing invariants are expressed in the indizies. -}
trun : ∀ {Γ Δ} → TStack Γ → TCode Γ Δ → TStack Δ
trun s (push v p) = trun (s ▹ v) p
trun (s ▹ nat n ▹ nat m) (+M p) = trun (s ▹ (nat (n + m))) p
trun (s ▹ nat n ▹ nat m) (≤M p) = trun (s ▹  bool (dec2bool (m ≤? n))) p
trun (s ▹ bool true) (branch p p') = trun s p
trun (s ▹ bool false) (branch p p') = trun s p'
trun s stop = s

{- the typed compiler is virtually identical to the untyped compiler
   but its type makes it clear that the code it generates leaves a
   value corresponding to the type of the expression on the stack.
-}
tcompile : ∀ {Γ Δ σ} → TExpr σ → TCode (Γ ▹ σ) Δ → TCode Γ Δ
tcompile (nat n) c = push (nat n) c
tcompile (bool b) c = push (bool b) c
tcompile (e +E e') c = tcompile e (tcompile e' (+M c))
tcompile (e ≤E e') c = tcompile e (tcompile e' (≤M c))
tcompile (ifE e then e' else e'') c = 
  tcompile e (branch (tcompile e' c) (tcompile e'' c))

{- typed compilation followed by running on the typed machine: -}
tcompileRun : ∀ {σ} → TExpr σ → TVal σ
tcompileRun e with trun ε (tcompile e stop)
...             | (_ ▹ v) = v

{- combining this with the type checker we obtan yet another way to
   execute untyped expression in an efficient and fast way. -}
checkCompileRun : Expr → Maybe Val
checkCompileRun e = infer e >>= λ c → return (⌊ tcompileRun (Check.te c)  ⌋v) 

{- extend the language by products:

  _,_ : Expr → Expr → Expr
  fst : Expr → Expr
  snd : Expr → Expr

extend the languages of values, extend the type checker and typed evaluator
and the typed assembly language and the compiler.
-}


