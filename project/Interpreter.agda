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
lookup (there p) η = lookup p (proj₁ η)

mutual
  -- Denotation of value subtyping
  coerceᵥ : ∀ {X Y} → X ⊑ᵥ Y → ⟦ X ⟧v → ⟦ Y ⟧v
  coerceᵥ ⊑ᵥ-ground A = A
  coerceᵥ (⊑ᵥ-product p q) (X , Y) = (coerceᵥ p X , coerceᵥ q Y)
  coerceᵥ (⊑ᵥ-Ufun p q) f = λ X' → coerceᵤ q (f (coerceᵥ p X'))
  coerceᵥ (⊑ᵥ-Kfun p q) f = λ X' → coerceₖ q (f (coerceᵥ p X'))
  coerceᵥ (⊑ᵥ-runner p q refl) r = λ op p' param C → include-tree q (r op (p _ p') param C) -- TODO: Make the first argument of p implicit

  -- Denotation of user computation subtyping
  coerceᵤ : ∀ {Xᵤ Yᵤ} → Xᵤ ⊑ᵤ Yᵤ → ⟦ Xᵤ ⟧u → ⟦ Yᵤ ⟧u
  coerceᵤ (⊑ᵤ-user p q) M = include-tree q (map-tree (coerceᵥ p) M)

  -- Denotation of kernel computation subtyping
  coerceₖ : ∀ {Xₖ Yₖ} → Xₖ ⊑ₖ Yₖ → ⟦ Xₖ ⟧k → ⟦ Yₖ ⟧k
  coerceₖ (⊑ₖ-kernel p q refl) K C = include-tree q (map-tree (λ {(X , C') → (coerceᵥ p X) , C'}) (K C))


-- Denotations of terms
mutual

--  sub-coop : ∀ { } →

  ⟦_⟧-value : ∀ {Γ X} → (Γ ⊢V: X) → ⟦ Γ ⟧-ctx → ⟦ X ⟧v
  ⟦ var x ⟧-value η = lookup x η
  ⟦ sub-value v x ⟧-value η = coerceᵥ x (⟦ v ⟧-value η)
  ⟦ ⟨⟩ ⟧-value η = tt
  ⟦ ⟨ v , w ⟩ ⟧-value η = (⟦ v ⟧-value η) , (⟦ w ⟧-value η)
  ⟦ funU m ⟧-value η = λ X → ⟦ m ⟧-user (η , X)
  ⟦ funK k ⟧-value η = λ X → ⟦ k ⟧-kernel (η , X)
  ⟦ runner r ⟧-value η = λ op x param → ⟦ (r op x) ⟧-kernel (η , param) --Removed C from the ends of this

  apply-runner : ∀ {Σ Σ' C X} → Runner Σ Σ' C → UComp Σ X → KComp Σ' C X
  apply-runner R (leaf x) c = leaf (x , c)
  apply-runner R (node op x param κ) = bind-kernel (apply-runner R ∘ κ) (R op x param)

  kernel-to-user : ∀ {Σ X Y C} → KComp Σ C X → C → (X × C → UComp Σ Y) → UComp Σ Y
  kernel-to-user k c m = bind-user m (k c)

  ⟦_⟧-user : ∀ {Γ Xᵤ} → (Γ ⊢U: Xᵤ) → ⟦ Γ ⟧-ctx → ⟦ Xᵤ ⟧u
  ⟦ sub-user m p ⟧-user η = coerceᵤ p (⟦ m ⟧-user η)
  ⟦ return v ⟧-user η = leaf (⟦ v ⟧-value η)
  ⟦ v · w ⟧-user η = ⟦ v ⟧-value η (⟦ w ⟧-value η)
  ⟦ opᵤ op p v m ⟧-user η = node op p (⟦ v ⟧-value η) λ res → ⟦ m ⟧-user (η , res)
  ⟦ `let m `in n ⟧-user η = bind-user (λ X → ⟦ n ⟧-user (η , X)) (⟦ m ⟧-user η)
  ⟦ match v `with m ⟧-user η = ⟦ m ⟧-user ((η , (proj₁ (⟦ v ⟧-value η))) , (proj₂ (⟦ v ⟧-value η)))
  ⟦ `using r at c `run m finally n ⟧-user η =
     kernel-to-user (apply-runner (⟦ r ⟧-value η) (⟦ m ⟧-user η)) (⟦ c ⟧-value η) (λ { (x , c') → ⟦ n ⟧-user ((η , x) , c')})
  ⟦ kernel k at c finally m ⟧-user η = kernel-to-user  (⟦ k ⟧-kernel η) (⟦ c ⟧-value η) (λ {(X , C) → ⟦ m ⟧-user ((η , X) , C)})

  ⟦_⟧-kernel : ∀ {Γ K} → (Γ ⊢K: K) → ⟦ Γ ⟧-ctx → ⟦ K ⟧k
  ⟦ sub-kernel k p ⟧-kernel η = coerceₖ p (⟦ k ⟧-kernel η)
  ⟦ return v ⟧-kernel η C = leaf ((⟦ v ⟧-value η) , C)
  ⟦ v · w ⟧-kernel η = ⟦ v ⟧-value η (⟦ w ⟧-value η)
  ⟦ `let k `in l ⟧-kernel η = bind-kernel (λ X → ⟦ l ⟧-kernel (η , X)) (⟦ k ⟧-kernel η)
  ⟦ match v `with k ⟧-kernel η = ⟦ k ⟧-kernel ((η , proj₁ (⟦ v ⟧-value η)) , proj₂ (⟦ v ⟧-value η))
  ⟦ opₖ op p v k ⟧-kernel η C =  node op p (⟦ v ⟧-value η) (λ res → ⟦ k ⟧-kernel (η , res) C)
  ⟦ getenv k ⟧-kernel η C = ⟦ k ⟧-kernel (η , C) C
  ⟦ setenv v k ⟧-kernel η _ = ⟦ k ⟧-kernel η (⟦ v ⟧-value η)
  ⟦ user m `with k ⟧-kernel η C = bind-user (λ X → ⟦ k ⟧-kernel (η , X) C) (⟦ m ⟧-user η)
