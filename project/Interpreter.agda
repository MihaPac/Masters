open import Data.Unit
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Function

import Contexts
open import Parameters
import Types
import Terms

module Interpreter (G : GTypes) (O : Ops G) where

open GTypes G
open Ops O

open Contexts G O
open Types G O
open Terms G O
open import Trees G O 

-- GENERAL TODO: naming conventions (think for yourself what to do, try to stay close to the paper/thesis)
-- - upper-case letters for types, lower-case letters for terms
-- - use X, Y, Z for value types
-- - use A, B, C for ground types
-- - something for base types? (could be 'b')
-- - use Xᵤ, Yᵤ, Zᵤ for user types
-- - use Xₖ, Yₖ, Zₖ  for kernel types

-- Trees are t, u, ...
-- UComps are M, N, ...
-- KComps are K, L, ...
-- Values are V, W, ...




mutual
  -- Denotation of value types

  ⟦_⟧v : VType → Set

  ⟦ gnd A ⟧v = ⟦ A ⟧g
  ⟦ X ×v Y ⟧v = ⟦ X ⟧v × ⟦ Y ⟧v
  ⟦ X ⟶ᵤ Y ⟧v = ⟦ X ⟧v → ⟦ Y ⟧u
  ⟦ X ⟶ₖ Y ⟧v = ⟦ X ⟧v → ⟦ Y ⟧k
  ⟦ Σ₁ ⇒ Σ₂ , C ⟧v = Runner Σ₁ Σ₂ ⟦ C ⟧g

  -- Denotation of a runner
  Runner : Sig → Sig → Set → Set
  Runner Σ₁ Σ₂ C = ∀ (op : Op) → op ∈ₒ Σ₁ → ⟦ param op ⟧g → KComp Σ₂ C ⟦ result op ⟧g

  -- Denotation of user computation types
  -- Idea: the elements of t!Σ are computations, each computation
  -- either returns a value of type t, or triggers an operation in Σ
  -- This is described by a *computation tree*:
  -- * leaves: return value
  -- * tree node: labeled by an operation and a parameter,
  --              subtrees are computations
  ⟦_⟧u : UType → Set
  ⟦ X ! Σ ⟧u = UComp Σ ⟦ X ⟧v

  -- Denotation of kernel computation types
  ⟦_⟧k : KType → Set
  ⟦ X ↯ Σ , C ⟧k = KComp Σ ⟦ C ⟧g ⟦ X ⟧v

-- Denotation of contexts are runtime environments

⟦_⟧-ctx : Ctx → Set
⟦ [] ⟧-ctx = ⊤
⟦ Γ ∷ X ⟧-ctx = ⟦ Γ ⟧-ctx × ⟦ X ⟧v

-- Lookup a variable in a runtime environment
lookup : ∀ {Γ X} (x : X ∈ Γ) → ⟦ Γ ⟧-ctx → ⟦ X ⟧v
lookup here η = proj₂ η
lookup (there x) η = lookup x (proj₁ η)

mutual
  -- Denotation of value subtyping
  coerceᵥ : ∀ {X Y} → X ⊑ᵥ Y → ⟦ X ⟧v → ⟦ Y ⟧v
  coerceᵥ ⊑ᵥ-ground A = A
  coerceᵥ (⊑ᵥ-product p q) (X , Y) = (coerceᵥ p X , coerceᵥ q Y)
  coerceᵥ (⊑ᵥ-Ufun p q) f = λ X' → coerceᵤ q (f (coerceᵥ p X'))
  coerceᵥ (⊑ᵥ-Kfun p q) f = λ X' → coerceₖ q (f (coerceᵥ p X'))
  coerceᵥ (⊑ᵥ-runner p q refl) R = λ op x param C → coerce-tree q (R op (p _ x) param C)
  
  -- Denotation of user computation subtyping
  coerceᵤ : ∀ {Xᵤ Yᵤ} → Xᵤ ⊑ᵤ Yᵤ → ⟦ Xᵤ ⟧u → ⟦ Yᵤ ⟧u
  coerceᵤ (⊑ᵤ-user p q) M = coerce-tree q (map-tree (coerceᵥ p) M)

  -- Denotation of kernel computation subtyping
  coerceₖ : ∀ {Xₖ Yₖ} → Xₖ ⊑ₖ Yₖ → ⟦ Xₖ ⟧k → ⟦ Yₖ ⟧k
  coerceₖ (⊑ₖ-kernel p q refl) K L = coerce-tree q (map-tree (λ {(X , C) → (coerceᵥ p X) , C}) (K L))


-- Denotations of terms
mutual

--  sub-coop : ∀ { } →

  ⟦_⟧-value : ∀ {Γ X} → (Γ ⊢V: X) → ⟦ Γ ⟧-ctx → ⟦ X ⟧v
  ⟦ var x ⟧-value η = lookup x η
  ⟦ sub-value V p ⟧-value η = coerceᵥ p (⟦ V ⟧-value η)
  ⟦ ⟨⟩ ⟧-value η = tt
  ⟦ ⟨ V , W ⟩ ⟧-value η = (⟦ V ⟧-value η) , (⟦ W ⟧-value η)
  ⟦ funU M ⟧-value η = λ X → ⟦ M ⟧-user (η , X)
  ⟦ funK K ⟧-value η = λ X → ⟦ K ⟧-kernel (η , X)
  ⟦ runner R ⟧-value η = λ op x param → ⟦ (R op x) ⟧-kernel (η , param)

  apply-runner : ∀ {Σ Σ' C X} → Runner Σ Σ' C → UComp Σ X → KComp Σ' C X
  apply-runner R (leaf x) = λ C → leaf (x , C)
  apply-runner R (node op x param κ) = bind-kernel (apply-runner R ∘ κ) (R op x param)

  kernel-to-user : ∀ {Σ X Y C} → KComp Σ C X → C → (X × C → UComp Σ Y) → UComp Σ Y
  kernel-to-user K C f = bind-user f (K C)

  ⟦_⟧-user : ∀ {Γ Xᵤ} → (Γ ⊢U: Xᵤ) → ⟦ Γ ⟧-ctx → ⟦ Xᵤ ⟧u
  ⟦ sub-user M p ⟧-user η = coerceᵤ p (⟦ M ⟧-user η)
  ⟦ return V ⟧-user η = leaf (⟦ V ⟧-value η)
  ⟦ V · W ⟧-user η = ⟦ V ⟧-value η (⟦ W ⟧-value η)
  ⟦ opᵤ op x V M ⟧-user η = node op x (⟦ V ⟧-value η) λ res → ⟦ M ⟧-user (η , res)
  ⟦ `let M `in N ⟧-user η = bind-user (λ X → ⟦ N ⟧-user (η , X)) (⟦ M ⟧-user η)
  ⟦ match V `with M ⟧-user η = ⟦ M ⟧-user ((η , (proj₁ (⟦ V ⟧-value η))) , (proj₂ (⟦ V ⟧-value η)))
  ⟦ `using R at C `run M finally N ⟧-user η =
      kernel-to-user (apply-runner (⟦ R ⟧-value η) (⟦ M ⟧-user η)) (⟦ C ⟧-value η) (λ { (X , C') → ⟦ N ⟧-user ((η , X) , C')})
  ⟦ kernel K at C finally M ⟧-user η = kernel-to-user  (⟦ K ⟧-kernel η) (⟦ C ⟧-value η) (λ {(X , C) → ⟦ M ⟧-user ((η , X) , C)})

  ⟦_⟧-kernel : ∀ {Γ K} → (Γ ⊢K: K) → ⟦ Γ ⟧-ctx → ⟦ K ⟧k
  ⟦ sub-kernel K p ⟧-kernel η = coerceₖ p (⟦ K ⟧-kernel η)
  ⟦ return V ⟧-kernel η C = leaf ((⟦ V ⟧-value η) , C)
  ⟦ V · W ⟧-kernel η = ⟦ V ⟧-value η (⟦ W ⟧-value η)
  ⟦ `let K `in L ⟧-kernel η = bind-kernel (λ X → ⟦ L ⟧-kernel (η , X)) (⟦ K ⟧-kernel η)
  ⟦ match V `with K ⟧-kernel η = ⟦ K ⟧-kernel ((η , proj₁ (⟦ V ⟧-value η)) , proj₂ (⟦ V ⟧-value η))
  ⟦ opₖ op x V K ⟧-kernel η C =  node op x (⟦ V ⟧-value η) (λ res → ⟦ K ⟧-kernel (η , res) C)
  ⟦ getenv K ⟧-kernel η C = ⟦ K ⟧-kernel (η , C) C
  ⟦ setenv V K ⟧-kernel η _ = ⟦ K ⟧-kernel η (⟦ V ⟧-value η)
  ⟦ user M `with K ⟧-kernel η C = bind-user (λ X → ⟦ K ⟧-kernel (η , X) C) (⟦ M ⟧-user η)
