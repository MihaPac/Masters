{- open import Level        renaming (zero to lzero; suc to lsuc)
import Contexts
open import Parameters
import Types
import Terms
import Monads
import Equations
import Denotations
import Sub-Validity
import Ren-Validity

module Examples2 (G : GTypes) (O : Ops G) where

open GTypes G
open Ops O

open Contexts G O
open Types G O
open Terms G O
open Monads G O
open Equations G O
open Denotations G O 
open import Renaming G O 
open import Substitution G O
open Sub-Validity G O
open Ren-Validity G O

open import Data.Nat.Base
open import Validity

fun1 : ℕ → ℕ → ℕ
fun1 n m = (2 * n) + m

fun2 : ℕ → ℕ → (ℕ → ℕ → ℕ) → ℕ
fun2 n m f = f n m 

Nats : {!   !} GTypes
Nats = {! record { Basetype = ? }  !}    -}

open import Data.Nat
open import Data.Bool
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality


open import Parameters
import Contexts
import Types
import Terms
import Interpreter
open import Trees

-- An example toy language with ground types for
-- booleans and natural numbers

data ToyBase : Set where
  bool : ToyBase
  nat : ToyBase


⟦_⟧toy : ToyBase → Set
⟦ bool ⟧toy = Bool
⟦ nat ⟧toy = ℕ

toyGround : GTypes
toyGround = record { BaseType = ToyBase ; ⟦_⟧b = ⟦_⟧toy }

-- In our toy language we have two operations:
-- flip : unit → 𝕓 (idea: it returns a random bit)
-- print : 𝕟 → unit (idea: it prints a number to standard output)
-- add : 𝕟 → 𝕟 → 𝕟 (idea: adds two numbers)
-- lessthan : 𝕟 → 𝕟 → bool (idea: compares two numbers)
-- multiply : 𝕟 → 𝕟 → 𝕟 (idea: multiplies two numbers)

data ToyOp : Set where
  flip : ToyOp
  print : ToyOp
  add : ToyOp
  lessthan : ToyOp
  multiply : ToyOp

open GTypes

toyParam : ToyOp → GType toyGround
toyParam flip = unit
toyParam print = base nat
toyParam add = base nat ×b base nat
toyParam lessthan = base nat ×b base nat
toyParam multiply = base nat ×b base nat

toyResult : ToyOp → GType toyGround
toyResult flip = base bool
toyResult print = unit
toyResult add = base nat
toyResult lessthan = base bool
toyResult multiply = base nat

toyOps : Ops toyGround
toyOps = record { Op = ToyOp ; param = toyParam ; result = toyResult }

module _ where
  open Contexts toyGround toyOps
  open Types toyGround toyOps
  open Terms toyGround toyOps 
  open import Substitution toyGround toyOps

  claw : Sub ([] ∷ gnd (base nat ×b base nat) ∷ gnd (base nat)) ([] ∷ gnd (base nat ×b base nat)) 
  claw x = {!   !}

  cat : ([] ∷ gnd (base nat ×b base nat)) ⊢U: gnd (base nat) ! λ {flip → false
                                                                ; print → true
                                                                ; add → true
                                                                ; lessthan → false
                                                                ; multiply → true}
  cat = `let (opᵤ multiply refl (var here) (return (var here))) `in (opᵤ add refl {!  !} {!   !})

  open Interpreter toyGround toyOps

  hat = ⟦ cat ⟧-user (tt , 3 , 4)


{-

  
  -- Let us compute the result of running cow in the runtime environment {x : 3 , 4}
  open Interpreter toyGround toyOps

  milk = ⟦ cow ⟧-user (tt , 3 , 4)
  -- Normalization of milk (Ctrl-c Ctrl-n in Emacs)
  -- Result: node add refl (3 , 4) (λ res → leaf res)

   -- A user computation in context with one variable of type 𝕟
  -- Written in human form: x : 𝕟, y : 𝕓 ⊢ᵤ print {!   !}x, _. return ⟨⟩)
--  cow : [] ∷ gnd (base nat) ∷ gnd (base bool) ⊢U: (gnd unit ! λ { flip → false ; print → true})
--  cow = opᵤ print refl (var (there here)) (return ⟨⟩)

  -- Let us compute the result of running cow in the runtime environment {x : 42, y : false}
--  open Interpreter toyGround toyOps

--  milk = ⟦ cow ⟧-user ((tt , 42) , false)
  -- Normalization of milk (Ctrl-c Ctrl-n in Emacs)
  -- Result: node print refl 42 (λ res → leaf tt)

  -- Written in human form: x : nat, y : bool ⊢ᵤ flip (⟨⟩, c . print (42, _ . return c))
  dog : [] ∷ gnd (base nat) ∷ gnd (base bool) ⊢U: (gnd (base bool) ! λ { flip → true ; print → true
                                                                        ; add → false ; lessthan → false})
  dog = opᵤ flip refl ⟨⟩ (opᵤ print refl (var (there (there here))) (return (var (there here))))

  tail = ⟦ dog ⟧-user ((tt , 42) , false)
  -- Normalize tail: node flip refl tt (λ c → node print refl 42 (λ _ → leaf c))
-}