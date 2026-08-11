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
  bol : ToyBase
  nat : ToyBase

⟦_⟧toy : ToyBase → Set
⟦ bol ⟧toy = Bool
⟦ nat ⟧toy = ℕ

toyGround : GTypes
toyGround = record { BaseType = ToyBase ; ⟦_⟧b = ⟦_⟧toy }

-- In our toy language we have two operations:
-- flip : unit → bol (idea: it returns a random bit)
-- print : nat → unit (idea: it prints a number to standard output)

data ToyOp : Set where
  flip : ToyOp
  print : ToyOp

open GTypes

toyParam : ToyOp → GType toyGround
toyParam flip =  unit
toyParam print = base nat

toyResult : ToyOp → GType toyGround
toyResult flip =  base bol
toyResult print = unit

toyOps : Ops toyGround
toyOps = record { Op = ToyOp ; param = toyParam ; result = toyResult }

-- example program written in this language
module _ where
  open Contexts toyGround toyOps
  open Types toyGround toyOps
  open Terms toyGround toyOps

  -- A user computation in context with one variable of type nat
  -- Written in human form: x : nat, y : bol ⊢ᵤ print (x, _. return ⟨⟩)
  rattle : [] ∷ gnd (base nat) ∷ gnd (base bol) ⊢U: (gnd unit ! λ { flip → false ; print → true})
  rattle = opᵤ print refl (var (there here)) (return ⟨⟩)

  -- Let us compute the result of running cow in the runtime environment {x : 42, y : false}
  open Interpreter toyGround toyOps

  handle = ⟦ rattle ⟧-user ((tt , 42) , false)
  -- Normalization of rattle (Ctrl-c Ctrl-n in Emacs)
  -- Result: node print refl 42 (λ res → leaf tt)

  -- Written in human form: x : nat, y : bol ⊢ᵤ flip (⟨⟩, c . print (42, _ . return c))
  box : [] ∷ gnd (base nat) ∷ gnd (base bol) ⊢U: (gnd (base bol) ! λ { flip → true ; print → true})
  box = opᵤ flip refl ⟨⟩ (
    opᵤ print refl (var (there (there here))) (
      return (var (there here))))

  crank = ⟦ box ⟧-user ((tt , 42) , false)
  -- Normalize crank: node flip refl tt (λ c → node print refl 42 (λ _ → leaf c))
