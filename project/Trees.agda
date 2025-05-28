open import Data.Unit
open import Data.Product
--open import Relation.Binary.PropositionalEquality
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Function

import Contexts
open import Parameters
import Types
import Terms

module Trees (G : GTypes) (O : Ops G) where --TODO: Organize things into separate files (17. 12. 2024)

open import Level        renaming (zero to lzero; suc to lsuc)
open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

open GTypes G
open Ops O

open Contexts G O
open Types G O
open Terms G O

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

-- Denotation of ground types TODO: daj v primerno datoteko
⟦_⟧g : GType → Set
⟦ base b ⟧g =  ⟦ b ⟧b
⟦ unit ⟧g = ⊤
⟦ A ×b B ⟧g = ⟦ A ⟧g × ⟦ B ⟧g

-- A computation tree that hold values of type T in their leaves
data Tree  (Σ : Sig) (X : Set) : Set where
  leaf : X → Tree Σ X
  node : ∀ (op : Op) → (p : op ∈ₒ Σ) → (param : ⟦ param op ⟧g) → (t : (res : ⟦ result op ⟧g) → Tree Σ X) → Tree Σ X

aux : ∀{op Σ₁ Σ₂ } → op ∈ₒ Σ₁ → Σ₁ ⊆ₛ Σ₂ → op ∈ₒ Σ₂ -- auxilliary function for include-tree
aux {op} p q = q op p

include-tree : ∀ {Σ₁ Σ₂ X} → Σ₁ ⊆ₛ Σ₂ → Tree Σ₁ X → Tree Σ₂ X
include-tree p (leaf x) = leaf x
include-tree p (node op q param c) = node op (aux q p) param (λ res → include-tree p (c res))

-- Monadic bind for trees
bind-tree : ∀ {Σ X Y} → (X → Tree Σ Y) → Tree Σ X → Tree Σ Y
bind-tree f (leaf x) = f x
bind-tree f (node op p param c) = node op p param (λ res → bind-tree f (c res))

map-tree : ∀ {Σ X Y} → (X → Y) → Tree Σ X → Tree Σ Y
map-tree f t = bind-tree (leaf ∘ f) t

--The monad laws for trees (missing one law, but the one that's trivial)
tree-id : ∀ {X Σ} (t : Tree Σ X)
    → bind-tree leaf t ≡ t
tree-id {X} {Σ} (leaf x) = refl
tree-id {X} {Σ} (node op p param t) = cong (node op p param) 
    (fun-ext (λ res → tree-id {X = X} {Σ = Σ} (t res)))

bind-tree-assoc : {Σ : Sig} {X Y Z : Set} (c : Tree Σ X) (f : X → Tree Σ Y)
    (g : Y → Tree Σ Z) →
    bind-tree g (bind-tree f c) ≡ bind-tree (λ x → bind-tree g (f x)) c
bind-tree-assoc (leaf x) f g = refl
bind-tree-assoc (node op p param c) f g = cong (node op p param) (fun-ext (λ res → bind-tree-assoc (c res) f g))

-- Denotation of a user computation returning elements of X and performing operations Σ
UComp : Sig → Set → Set
UComp Σ X = Tree Σ X --TODO: Prove that THIS/Tree(X) is a Monad, the UComp will be T, bind is the bind-tree, leaf is the unit η,
--when verifying equations keep in mind that you might have to use funext

bind-user : ∀ {Σ X Y} → (X → UComp Σ Y) → UComp Σ X → UComp Σ Y
bind-user = bind-tree

-- Denotation of a kernel computation with state C returning elements of X
KComp : Sig → Set → Set → Set
KComp Σ C X = C → Tree Σ (X × C)
-- Monad1 - C → ? × C
-- Monad2 - Tree Σ ?
-- KComp is the combination of Monad1 and Monad2
-- TODO: Prove the Kernel is also a Monad (in this file, possibly)

bind-kernel : ∀ {Σ C X Y} → (X → KComp Σ C Y) → KComp Σ C X → KComp Σ C Y
bind-kernel f K C = bind-tree (λ {(x , C') → f x C'}) (K C)

