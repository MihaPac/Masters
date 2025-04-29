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
    -- carrier (object map) fo the Kleisli triple
    T       : Set → Set
    -- unit
    η       : {X : Set} → X → T X
    -- bind
    _>>=_   : {X Y : Set} → T X → (X → T Y) → T Y
    -- laws
    η-left  : {X Y : Set} (x : X) (f : X → T Y) → η x >>= f ≡ f x
    η-right : {X : Set} (c : T X) → c >>= η ≡ c
    >>=-assoc : {X Y Z : Set} (c : T X) (f : X → T Y) (g : Y → T Z)
              → ((c >>= f) >>= g) ≡ c >>= (λ x → f x >>= g)


η-right-Tree : {X : Set} {Σ : Sig} (c : Tree Σ X) → bind-tree leaf c ≡ c
η-right-Tree (leaf x) = refl
η-right-Tree (node op p param c) = cong (node op p param) (fun-ext (λ res → η-right-Tree (c res)))

>>=-assoc-Tree : {X Y Z : Set} {Σ : Sig} (c : Tree Σ X) (f : X → Tree Σ Y)
    (g : Y → Tree Σ Z) →
    bind-tree g (bind-tree f c) ≡ bind-tree (λ x → bind-tree g (f x)) c
>>=-assoc-Tree (leaf x) f g = refl
>>=-assoc-Tree (node op p param c) f g = cong (node op p param) (fun-ext (λ res → >>=-assoc-Tree (c res) f g))


TreeMonad : Monad {l}
TreeMonad   = record {
  T         = Tree Σ ;
  η         = leaf ;
  _>>=_     = λ x f → bind-tree f x ;
  η-left    = λ x f → refl ;
  -- (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
  η-right   = η-right-Tree ;
  >>=-assoc = >>=-assoc-Tree }


UMonad : Monad {l} --TODO: this is the same as TreeMonad
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
  η         = λ x c → leaf (x , c) ;
  _>>=_     = λ K f c → bind-kernel f K c ;
  η-left    = λ c f → refl ;
  η-right   = η-right-Kernel ;
  >>=-assoc = >>=-assoc-Kernel }
  where
    η-right-Kernel : {X : Set} (K : KComp Σ C X) → bind-kernel (λ x c → leaf (x , c)) K ≡ K --TODO: rename things as you go so that it makes sense
    η-right-Kernel K = fun-ext λ c → η-right-Tree (K c)

    >>=-assoc-Kernel : {X Y Z : Set} (K : KComp Σ C X) (f : X → KComp Σ C Y) (g : Y → KComp Σ C Z)
      → bind-kernel g (bind-kernel f K) ≡ bind-kernel (λ x → bind-kernel g (f x)) K
    >>=-assoc-Kernel K f g = fun-ext (λ c → >>=-assoc-Tree (K c) (λ { (x , c') → f x c' }) (λ { (y , c') → g y c' }))


--TODOs for next time (17. 12. 2024)
--1. Split Denotations.agda into 2 files, one file has all definitions regarding Monads, the other has the ⟦ ⟧ stuff, except the ⟦ ⟧g stuff (which goes with Monads).
--2. Use consistent fixed variable names. Then keep it consistent forevermore.
--3. Finish the definitions of the ⟦ ⟧-kernel and ⟦ ⟧-user
--- ^What is expected^ --
--3.5. Rewrite the ⟦ ⟧ stuff to use the Monad structure
--4. getenv, setenv and the equations they use (for the Kernel Monad), algebraic operations, algebraicity equation (for both monads)
--Optional: Read the literature already given. Most important is that the Runners paper is understood as much as possible, the rest is simply background reading to understand that.
--Keep track of things you do not understand. Danel's thesis will be useful for HOW to write your own thesis. The MFPS2013 paper will also be useful.
