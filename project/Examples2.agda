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
  --add : ToyOp
  --add : ToyOp
  --lessthan : ToyOp
  --multiply : ToyOp

open GTypes

toyParam : ToyOp → GType toyGround
toyParam flip = unit
toyParam print = base nat
--toyParam add = base nat ×b base nat
--toyParam add = base nat ×b base nat
--toyParam lessthan = base nat ×b base nat
--toyParam multiply = base nat ×b base nat

toyResult : ToyOp → GType toyGround
toyResult flip = base bool
toyResult print = unit
--toyResult add = base nat
--toyResult lessthan = base bool
--toyResult multiply = base nat

toyOps : Ops toyGround
toyOps = record { Op = ToyOp ; param = toyParam ; result = toyResult }

module _ where
  open Contexts toyGround toyOps
  open Types toyGround toyOps
  open Terms toyGround toyOps 
  open import Substitution toyGround toyOps

  claw : Sub ([] ∷ gnd (base nat ×b base nat) ∷ gnd (base nat)) ([] ∷ gnd (base nat ×b base nat)) 
  claw x = {!   !}

  product : ([] ∷ gnd (base nat)) ∷ gnd (base nat) ⊢V: (gnd (base nat) ×v gnd (base nat))
  product = ⟨ (var here) , (var (there here)) ⟩

  addition : [] ∷ (gnd (base nat) ×v gnd (base nat)) ⊢U: gnd (base nat) ! {!   !} 
  addition = {! funU ?  !}

  addition2 : {!   !} ⊢V: {!   !}
  addition2 = funU addition

{-
  -- Breaks up product
  matcher : ([] ∷ (gnd (base nat) ×v gnd (base nat))) ⊢V: {!   !}
  matcher = {!   !}

  addition : [] ∷ (gnd (base nat) ×v gnd (base nat)) ⊢V: (gnd (base nat)) --! {!   !})
  addition = {!   !} --match (var here) `with {!   !}

  addition2 : [] ∷ (gnd (base nat)) ∷ gnd (base nat) ⊢V: (gnd (base nat ×b base nat)) --! {!   !})
  addition2 = {!   !}

  addition3 : [] ∷ (gnd (base nat)) ∷ gnd (base nat) ⊢U: (gnd (base nat ×b base nat)) ! {!   !}
  addition3 = {!   !}

  addition4 : [] ∷ (gnd (base nat) ×v gnd (base nat)) ⊢U: (gnd (base nat ×b base nat)) ! {!   !}
  addition4 = match (var here) `with (return {!   !})

  poganjalec : co-op {!   !} {!   !} {!   !} {!   !}
  poganjalec = {!   !}
-}





  --uporabniška izračuna za mačko


  Sigma : Ops.Sig toyOps
  Sigma flip = false
  Sigma print = true

  Sigma' : Ops.Sig toyOps
  Sigma' flip = true
  Sigma' print = false 

  rat : [] ∷ gnd (base nat) ∷ gnd (base bool) ⊢V: ({!   !} ⇒ {!   !} , {!   !})
  rat = runner λ {flip x → return (var (there here))
                ; print x → return ⟨⟩}

  paw1 : [] ∷ gnd (base nat) ∷ gnd (base bool) ⊢U: (gnd unit ! Sigma)
  paw1 = opᵤ print refl (var (there here)) (return ⟨⟩)

  paw2 : (([] ∷ gnd (base nat) ∷ gnd (base bool)) ∷ gnd unit) ∷
    gnd unit ⊢U: ({!   !} ! Sigma')
  paw2 = opᵤ flip {!   !} {!   !} {!   !}
  
  cat : {!   !} ⊢U: ({!   !} ! Sigma')
  cat = `using rat at {!   !} `run paw1 finally paw2

{-
  paw1 : ([] ∷ gnd (base nat)) ⊢U: (gnd (base nat) ! Sigma)
  paw1 = return (var here)

  paw2 : [] ∷ gnd (base nat) ∷ gnd (base nat) ∷ gnd (base nat) ⊢U: (gnd unit ! Sigma')
  paw2 = opᵤ print refl (var (there here)) (return ⟨⟩)

-- Če pravilno razumem, bomo lahko uporabili drugačne sigme za run, in potem 
  cat : ([] ∷ gnd (base nat)) ⊢U: (gnd unit ! Sigma') 
  cat = `using rat at var here `run paw1 finally paw2
  open Interpreter toyGround toyOps

--  hat = ⟦ cat ⟧-user (tt , 3 , 4)

  bag = ⟦ cat ⟧-user (tt , 10) --⟦ cat ⟧-user (tt , 10)

-}

{-
  cat : ([] ∷ gnd (base nat ×b base nat)) ⊢U: gnd (base nat) ! λ {flip → false
                                                                ; print → true
                                                                ; add → true
                                                                ; lessthan → false
                                                                ; multiply → true}
  cat = `let (opᵤ multiply refl (var here) (return (var here))) `in {!   !}
  --(opᵤ add refl {! _·_  !} {!   !})
-}
