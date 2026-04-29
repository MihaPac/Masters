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

module Trees (G : GTypes) (O : Ops G) where

open import Level        renaming (zero to lzero; suc to lsuc)
open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b

open GTypes G
open Ops O

open Contexts G O
open Types G O
open Terms G O

⟦_⟧g : GType → Set
⟦ base b ⟧g =  ⟦ b ⟧b
⟦ unit ⟧g = ⊤
⟦ A ×b B ⟧g = ⟦ A ⟧g × ⟦ B ⟧g

-- A computation tree that hold values of type T in their leaves
data Tree  (Σ : Sig) (X : Set) : Set where
  leaf : X → Tree Σ X
  node : ∀ (op : Op) → (x : op ∈ₒ Σ) → (param : ⟦ param op ⟧g) 
    → (t : (res : ⟦ result op ⟧g) → Tree Σ X) → Tree Σ X

coerce-signature : ∀{op Σ₁ Σ₂ } → op ∈ₒ Σ₁ → Σ₁ ⊆ₛ Σ₂ → op ∈ₒ Σ₂ -- auxilliary function for coerce-tree
coerce-signature {op} x p = p op x

coerce-tree : ∀ {Σ₁ Σ₂ X} → Σ₁ ⊆ₛ Σ₂ → Tree Σ₁ X → Tree Σ₂ X
coerce-tree p (leaf x) = leaf x
coerce-tree p (node op x param C) = 
    node op (coerce-signature x p) param (λ res → coerce-tree p (C res))

-- Monadic bind for trees
bind-tree : ∀ {Σ X Y} → (X → Tree Σ Y) → Tree Σ X → Tree Σ Y
bind-tree f (leaf x) = f x
bind-tree f (node op x param C) = node op x param (λ res → bind-tree f (C res))

map-tree : ∀ {Σ X Y} → (X → Y) → Tree Σ X → Tree Σ Y
map-tree f t = bind-tree (leaf ∘ f) t

--The monad laws for trees (missing one law, but the one that's trivial)
tree-id : ∀ {X Σ} (t : Tree Σ X)
    → bind-tree leaf t ≡ t
tree-id {X} {Σ} (leaf x) = refl
tree-id {X} {Σ} (node op x param t) = cong (node op x param) 
    (fun-ext (λ res → tree-id {X = X} {Σ = Σ} (t res)))

bind-tree-assoc : {Σ : Sig} {X Y Z : Set} (t : Tree Σ X) (f : X → Tree Σ Y)
    (g : Y → Tree Σ Z) →
    bind-tree g (bind-tree f t) ≡ bind-tree (λ x → bind-tree g (f x)) t
bind-tree-assoc (leaf x) f g = refl
bind-tree-assoc (node op x param C) f g = 
    cong (node op x param) (fun-ext (λ res → bind-tree-assoc (C res) f g))

-- Denotation of a user computation returning elements of X and performing operations Σ
UComp : Sig → Set → Set
UComp Σ X = Tree Σ X 

bind-user : ∀ {Σ X Y} → (X → UComp Σ Y) → UComp Σ X → UComp Σ Y
bind-user = bind-tree

-- Denotation of a kernel computation with state C returning elements of X
KComp : Sig → Set → Set → Set
KComp Σ C X = C → Tree Σ (X × C)
-- Monad1 - C → ? × C
-- Monad2 - Tree Σ ?
-- KComp is the combination of Monad1 and Monad2

bind-kernel : ∀ {Σ C X Y} → (X → KComp Σ C Y) → KComp Σ C X → KComp Σ C Y
bind-kernel f K C = bind-tree (λ {(x , C') → f x C'}) (K C)

