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
  𝕓 : ToyBase
  𝕟 : ToyBase

⟦_⟧toy : ToyBase → Set
⟦ 𝕓 ⟧toy = Bool
⟦ 𝕟 ⟧toy = ℕ

toyGround : GTypes
toyGround = record { BaseType = ToyBase ; ⟦_⟧b = ⟦_⟧toy }

-- In our toy language we have two operations:
-- flip : unit → 𝕓 (idea: it returns a random bit)
-- print : 𝕟 → unit (idea: it prints a number to standard output)

data ToyOp : Set where
  flip : ToyOp
  print : ToyOp

open GTypes

toyParam : ToyOp → GType toyGround
toyParam flip =  unit
toyParam print = base 𝕟

toyResult : ToyOp → GType toyGround
toyResult flip =  base 𝕓
toyResult print = unit

toyOps : Ops toyGround
toyOps = record { Op = ToyOp ; param = toyParam ; result = toyResult }

-- example program written in this language
module _ where
  open Contexts toyGround toyOps
  open Types toyGround toyOps
  open Terms toyGround toyOps

  -- A user computation in context with one variable of type 𝕟
  -- Written in human form: x : 𝕟, y : 𝕓 ⊢ᵤ print (x, _. return ⟨⟩)
  cow : [] ∷ gnd (base 𝕟) ∷ gnd (base 𝕓) ⊢U: (gnd unit ! λ { flip → false ; print → true})
  cow = opᵤ print refl (var (there here)) (return ⟨⟩)

  -- Let us compute the result of running cow in the runtime environment {x : 42, y : false}
  open Interpreter toyGround toyOps

  milk = ⟦ cow ⟧-user ((tt , 42) , false)
  -- Normalization of milk (Ctrl-c Ctrl-n in Emacs)
  -- Result: node print refl 42 (λ res → leaf tt)

  -- Written in human form: x : 𝕟, y : 𝕓 ⊢ᵤ flip (⟨⟩, c . print (42, _ . return c))
  dog : [] ∷ gnd (base 𝕟) ∷ gnd (base 𝕓) ⊢U: (gnd (base 𝕓) ! λ { flip → true ; print → true})
  dog = opᵤ flip refl ⟨⟩ (opᵤ print refl (var (there (there here))) (return (var (there here))))

  tail = ⟦ dog ⟧-user ((tt , 42) , false)
  -- Normalize tail: node flip refl tt (λ c → node print refl 42 (λ _ → leaf c))
