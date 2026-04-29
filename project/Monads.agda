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

module Monads (G : GTypes) (O : Ops G) {Σ} {l} where 


open import Level        renaming (zero to lzero; suc to lsuc)

open GTypes G
open Ops O

open Contexts G O
open Types G O
open Terms G O
open import Trees G O 


record Monad {l} : Set (lsuc l) where
  field
    -- carrier (object map) for the Kleisli triple
    T       : Set → Set
    -- unit
    η       : {X : Set} → X → T X
    -- bind
    _>>=_   : {X Y : Set} → T X → (X → T Y) → T Y
    -- laws
    η-left  : {X Y : Set} (x : X) (f : X → T Y) 
      → η x >>= f ≡ f x
    η-right : {X : Set} (t : T X) 
      → t >>= η ≡ t
    >>=-assoc : {X Y Z : Set} (t : T X) 
      (f : X → T Y) (g : Y → T Z)
      → ((t >>= f) >>= g) ≡ t >>= (λ x → f x >>= g)


η-right-Tree : {X : Set} {Σ : Sig} (t : Tree Σ X) → bind-tree leaf t ≡ t
η-right-Tree (leaf x) = refl
η-right-Tree (node op x param t) = 
  cong (node op x param) (fun-ext (λ res → η-right-Tree (t res)))

>>=-assoc-Tree : {X Y Z : Set} {Σ : Sig} (t : Tree Σ X) (f : X → Tree Σ Y)
    (g : Y → Tree Σ Z) →
    bind-tree g (bind-tree f t) ≡ bind-tree (λ x → bind-tree g (f x)) t
>>=-assoc-Tree (leaf x) f g = refl
>>=-assoc-Tree (node op x param t) f g = 
  cong (node op x param) (fun-ext (λ res → >>=-assoc-Tree (t res) f g))


TreeMonad : Monad {l}
TreeMonad   = record {
  T         = Tree Σ ;
  η         = leaf ;
  _>>=_     = λ x f → bind-tree f x ;
  η-left    = λ x f → refl ;
  -- (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
  η-right   = η-right-Tree ;
  >>=-assoc = >>=-assoc-Tree }


UMonad : Monad {l} 
UMonad = record {
  T         = UComp Σ ;
  η         = leaf ;
  _>>=_     = λ M f → bind-user f M ;
  η-left    = λ x f → refl ;
  η-right   = η-right-Tree ;
  >>=-assoc = >>=-assoc-Tree }


KMonad : (C : Set) → Monad {l}
KMonad C = record {
  T         = KComp Σ C ;
  η         = λ x C → leaf (x , C) ;
  _>>=_     = λ K f C → bind-kernel f K C ;
  η-left    = λ x f → refl ;--λ C f → refl ;
  η-right   = η-right-Kernel ;
  >>=-assoc = >>=-assoc-Kernel }
  where
    η-right-Kernel : {X : Set} (K : KComp Σ C X) 
      → bind-kernel (λ x C → leaf (x , C)) K ≡ K 
    η-right-Kernel K = fun-ext λ C → η-right-Tree (K C)

    >>=-assoc-Kernel : {X Y Z : Set} (K : KComp Σ C X) 
      (f : X → KComp Σ C Y) (g : Y → KComp Σ C Z)
      → bind-kernel g (bind-kernel f K) ≡ 
        bind-kernel (λ x → bind-kernel g (f x)) K
    >>=-assoc-Kernel K f g = 
      fun-ext (λ C → 
        >>=-assoc-Tree 
          (K C) 
          (λ { (x , C') → f x C' }) 
          (λ { (y , C') → g y C' }))