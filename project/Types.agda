open import Data.Bool
open import Relation.Binary.PropositionalEquality

open import Parameters

module Types (G : GTypes) (O : Ops G) where

open GTypes G
open Ops O

-- Kernel state type
KState = GType

interleaved mutual
  data VType : Set
  data UType : Set
  data KType : Set

  -- Value type
  data VType where
    gnd   : GType → VType
    _×v_   : VType → VType → VType -- Written as "\x"
    _⟶ᵤ_  : VType → UType → VType -- "\r--"
    _⟶ₖ_  : VType → KType → VType
    _⇒_,_ : Sig → Sig → KState → VType -- "\r="

  --- User type
  data UType where
    _!_ : VType → Sig → UType

  --- Kernel Type
  data KType where
    _↯_,_ : VType → Sig → KState → KType   --"\dz = ↯"


-- Subtyping relations
_⊆ₛ_ : Sig → Sig → Set
Σ ⊆ₛ Σ' = (op : Op) → Σ op ≡ true → Σ' op ≡ true -- TODO; can we make op implicit?

_≡ₖ_ : KState → KState → Set
C ≡ₖ C' = C ≡ C'

interleaved mutual
  data _⊑ᵥ_ : VType → VType → Set
  data _⊑ᵤ_ : UType → UType → Set
  data _⊑ₖ_ : KType → KType → Set

  data _⊑ᵥ_ where -- "\squb="

    ⊑ᵥ-ground : {A : GType}
              -------------
              → gnd A ⊑ᵥ gnd A

    ⊑ᵥ-product : {X Y X' Y' : VType}
               → X ⊑ᵥ X'
               → Y ⊑ᵥ Y'
               --------------------
                 → (X ×v Y) ⊑ᵥ (X' ×v Y')


    ⊑ᵥ-Ufun : {X X' : VType} {Σ Σ' : UType}
    --TODO: Contemplate this one
                → X' ⊑ᵥ X
                → Σ ⊑ᵤ Σ'
                -----------------------
                → X ⟶ᵤ Σ ⊑ᵥ X' ⟶ᵤ Σ'

    ⊑ᵥ-Kfun : {X X' : VType} {Xₖ Xₖ' : KType}
                → X' ⊑ᵥ X
                → Xₖ ⊑ₖ Xₖ'
                -----------------------------------
                → X ⟶ₖ Xₖ ⊑ᵥ X' ⟶ₖ Xₖ'

    ⊑ᵥ-runner : {Σ₁ Σ₁' Σ₂ Σ₂' : Sig} {C C' : KState}
               → Σ₁' ⊆ₛ Σ₁
               → Σ₂ ⊆ₛ Σ₂'
               → C ≡ C'
               --------------
               → Σ₁ ⇒ Σ₂ , C ⊑ᵥ Σ₁' ⇒ Σ₂' , C'

  data _⊑ᵤ_ where


    ⊑ᵤ-user : {X X' : VType} {Σ Σ' : Sig}
                → X ⊑ᵥ X'
                → Σ ⊆ₛ Σ'
                → X ! Σ ⊑ᵤ X' ! Σ'

  data _⊑ₖ_ where



    ⊑ₖ-kernel : {X X' : VType} {Σ Σ' : Sig} {C C' : KState}
                → X ⊑ᵥ X'
                → Σ ⊆ₛ Σ'
                → C ≡ C'
                ---------------------------
                → X ↯ Σ , C ⊑ₖ X' ↯ Σ' , C'




infix 12 _⟶ᵤ_ _⟶ₖ_ _⇒_,_
infix 10 _⊑ᵥ_ _⊑ᵤ_ _⊑ₖ_
infix 15 _!_ _↯_,_
infix 40 _×v_
