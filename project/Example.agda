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
  boo : ToyBase
  nat : ToyBase

⟦_⟧toy : ToyBase → Set
⟦ boo ⟧toy = Bool
⟦ nat ⟧toy = ℕ

toyGround : GTypes
toyGround = record { BaseType = ToyBase ; ⟦_⟧b = ⟦_⟧toy }

-- In our toy language we have two operations:
-- flip : unit → boo (idea: it returns a random bit)
-- print : nat → unit (idea: it prints a number to standard output)

data ToyOp : Set where
  flip : ToyOp
  print : ToyOp

open GTypes

toyParam : ToyOp → GType toyGround
toyParam flip =  unit
toyParam print = base nat

toyResult : ToyOp → GType toyGround
toyResult flip =  base boo
toyResult print = unit

toyOps : Ops toyGround
toyOps = record { Op = ToyOp ; param = toyParam ; result = toyResult }

-- example program written in this language
module _ where
  open Contexts toyGround toyOps
  open Types toyGround toyOps
  open Terms toyGround toyOps

  -- A user computation in context with one variable of type nat
  -- Written in human form: x : nat, y : boo ⊢ᵤ print (x, _. return ⟨⟩)
  rattle : [] ∷ gnd (base nat) ∷ gnd (base boo) ⊢U: (gnd unit ! λ { flip → false ; print → true})
  rattle = opᵤ print refl (var (there here)) (return ⟨⟩)

  -- Let us compute the result of running cow in the runtime environment {x : 42, y : false}
  open Interpreter toyGround toyOps

  handle = ⟦ rattle ⟧-user ((tt , 42) , false)
  -- Normalization of rattle (Ctrl-c Ctrl-n in Emacs)
  -- Result: node print refl 42 (λ res → leaf tt)

  -- Written in human form: x : nat, y : boo ⊢ᵤ flip (⟨⟩, c . print (42, _ . return c))
  box : [] ∷ gnd (base nat) ∷ gnd (base boo) ⊢U: (gnd (base boo) ! λ { flip → true ; print → true})
  box = opᵤ flip refl ⟨⟩ (
    opᵤ print refl (var (there (there here))) (
      return (var (there here))))

  crank = ⟦ box ⟧-user ((tt , 42) , false)
  -- Normalize crank: node flip refl tt (λ c → node print refl 42 (λ _ → leaf c))



  Sigma : Ops.Sig toyOps
  Sigma flip = true
  Sigma print = false

  doubler : [] ∷ gnd unit ⊢V: (Sigma ⇒ Sigma , unit)
  doubler = runner λ {flip x → opₖ flip x ⟨⟩ (opₖ flip x ⟨⟩ (return (var here)))
                ; print x → return ⟨⟩ }

  one : [] ∷ gnd unit ⊢U: (gnd (base boo) ! Sigma)
  one = opᵤ flip refl ⟨⟩ (return (var here))

  onetwo = ⟦ one ⟧-user (tt , tt)

  two : [] ∷ gnd unit ⊢U: (gnd unit ! Sigma)
  two = `using doubler at ⟨⟩ `run one finally (return ⟨⟩)

  twotwo = ⟦ two ⟧-user (tt , tt)

  three : [] ∷ gnd unit ⊢U: (gnd unit ! Sigma)
  three = `using doubler at ⟨⟩ `run two finally (return ⟨⟩)

  threetwo = ⟦ three ⟧-user (tt , tt)


-- onetwo - node flip refl tt (λ res → leaf tt)
-- twotwo - node flip refl tt (λ res → node flip refl tt (λ res₁ → leaf tt))
-- threetwo - node flip refl tt (λ res →
--    node flip refl tt
--    (λ res₁ →
--        node flip refl tt (λ res₂ → node flip refl tt (λ res₃ → leaf tt))))

{-
  paw1 : [] ∷ gnd (base nat) ∷ gnd (base boo) ⊢U: (gnd unit ! Sigma)
  paw1 = opᵤ print refl (var (there here)) (return ⟨⟩)

  paw2 : (([] ∷ gnd (base nat) ∷ gnd (base boo)) ∷ gnd unit) ∷
    gnd unit ⊢U: ({!   !} ! Sigma')
  paw2 = opᵤ flip {!   !} {!   !} {!   !}


  cat : {!   !} ⊢U: ({!   !} ! Sigma')
  cat = `using doubler at {!   !} `run paw1 finally paw2
  -}
