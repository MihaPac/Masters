--{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning     -- using ( _≡⟨⟩_ ; _∎ ; begin_) renaming (begin_ to start_ ; step-≡ to step-= ) 
--(begin_ to start_ ; _≡⟨⟩_ to _=<>_ ; step-≡ to step-= ; _∎ to _qed) 
-- using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Function

import Contexts
open import Parameters
import Types
import Terms
import Monads
import Equations
import Denotations

module Sub-Validity (G : GTypes) (O : Ops G) where

open GTypes G
open Ops O

open Contexts G O
open Types G O
open Terms G O
open Monads G O
open Equations G O
open Denotations G O 
open import Renaming G O 
open import Substitution G O

{-Tezave:
Kako delati karkoli z "extend sigma"-}

mutual
-- Naming scheme for the various equalities:
--   Γ ⊢V v ≡ w will be named eq-v, eq-w, ...
--   Γ ⊢U m ≡ n will be named eq-m, eq-n, ...
--   Γ ⊢K k ≡ l will be named eq-k, eq-l, ...
-- This naming scheme will be to quickly show the type of equivalence.

    ⟦_⟧-sub : ∀ {Γ Γ'} → Sub Γ Γ' → ⟦ Γ ⟧-ctx → ⟦ Γ' ⟧-ctx  
    ⟦_⟧-sub {Γ' = []} σ η = tt
    ⟦_⟧-sub {Γ' = Γ' ∷ X} σ η = (⟦ σ ∘ there ⟧-sub η) , ⟦ σ here ⟧-value η

    ⟦_⟧-ren : ∀ {Γ Γ'} → Ren Γ Γ' → ⟦ Γ ⟧-ctx → ⟦ Γ' ⟧-ctx
    ⟦_⟧-ren {Γ' = []} ρ η = tt
    ⟦_⟧-ren {Γ' = Γ' ∷ X} ρ η = ⟦ ρ ∘ there ⟧-ren η , lookup (ρ here) η


    to-sub : ∀ {Γ Γ'} 
        → Ren Γ Γ' → Sub Γ Γ'
    to-sub ρ x = var (ρ x) 

    sub-to-ren : ∀ {Γ Γ'} → (ρ : Ren Γ Γ') → (η : ⟦ Γ ⟧-ctx) 
        → ⟦ to-sub ρ ⟧-sub η ≡ ⟦ ρ ⟧-ren η
    sub-to-ren {Γ} {[]} ρ η = refl
    sub-to-ren {Γ} {Γ' ∷ X} ρ η = cong₂ _,_ (sub-to-ren (ρ ∘ there) η) refl

    ren-env : ∀ {Γ Γ' X} {ρ : Ren Γ Γ'} {η : ⟦ Γ ⟧-ctx} → (x : X ∈ Γ') 
        → lookup x (⟦ ρ ⟧-ren η) ≡ lookup (ρ x) η
    ren-env {Γ} {Γ'} {X} {ρ} {η} here = refl
    ren-env {Γ} {Γ'} {X} {ρ} {η} (there x) = ren-env {ρ = ρ ∘ there} x

    lookup-ext : ∀ {Γ} {η η' : ⟦ Γ ⟧-ctx} → (∀ {X} (x : X ∈ Γ) 
        → lookup x η ≡ lookup x η') → η ≡ η'
    lookup-ext {[]} {η} {η'} eq = refl
    lookup-ext {Γ ∷ X} {η , v} {η' , v'} eq = cong₂ _,_ (lookup-ext (eq ∘ there))  (eq here)
    --Maybe a lemma for cong₂ _,_ or maybe it's in the standard library

    sub-var : ∀ { Γ } {η : ⟦ Γ ⟧-ctx} 
        → η ≡ ⟦ var ⟧-sub η
    sub-var {Γ} {η} = Eq.trans (lookup-ext (λ x → Eq.sym (ren-env {ρ = idᵣ} x))) (Eq.sym (sub-to-ren idᵣ η))

-- NOODLING AROUND

    aux-there : ∀ { Γ Γ' } {g : ⟦ {!   !} ⟧b} {v : VType} (ρ : Ren Γ (Γ' ∷ v)) (η : ⟦ Γ ⟧-ctx) 
        → ⟦ to-sub ρ ⟧-sub η ≡ ⟦ to-sub (ρ ∘ᵣ there) ⟧-sub (η , g) 
        --there : {X Y : VType} {Γ : Ctx} → X ∈ Γ → X ∈ (Γ ∷ Y)
    aux-there {Γ} {[]} {g} {v} ρ η = cong₂ _,_ refl refl
    aux-there {Γ} {Γ' ∷ X} {g} {v} ρ η = cong₂ _,_ (aux-there {g = {!   !}} {v = X} (there ∘ᵣ ρ) η) refl

    {-aux-there' : ∀ { Γ Γ' } (σ : Sub Γ Γ')  (η : ⟦ {!   !} ⟧-ctx) --(η' : ⟦ Γ ⟧-ctx)
        → ⟦ σ ⟧-sub (⟦ wkᵣ ⟧-ren η) ≡ ⟦ wkᵣ ᵣ∘ₛ σ ⟧-sub η
    aux-there' {Γ} {Γ'} σ η = aux-thera wkᵣ σ η  -}

    --⟦ σ ⟧-sub η ≡ ⟦ (λ x → σ x [ wkᵣ ]ᵥᵣ) ⟧-sub (η , res)
    aux-there'' : ∀ { Γ Γ' res} (σ : Sub Γ Γ')  (η : ⟦ {!   !} ⟧-ctx) --(η' : ⟦ Γ ⟧-ctx)
        → ⟦ σ ⟧-sub η ≡ ⟦ (λ x → σ x [ wkᵣ ]ᵥᵣ) ⟧-sub (η , res)
    aux-there'' {Γ} {Γ'} σ η = 
        Eq.trans 
            (cong₂ ⟦_⟧-sub 
                {!   !} 
                {!   !}) 
            {!   !}

    help : ∀ {Γ} (η : ⟦ Γ ⟧-ctx)  
        → η ≡ ⟦ {! wkᵣ  !} ⟧-ren {!   !}
    help = {! begin_  !}

    --sub-ren?
    --sub-ren-V
    --sub-ren-U
    --sub-ren-K
    sub-ren : ∀ { Γ Γ' Γ'' } (ρ : Ren Γ Γ') (σ : Sub Γ' Γ'')  (η : ⟦ Γ ⟧-ctx) --(η' : ⟦ Γ ⟧-ctx)
        → ⟦ σ ⟧-sub (⟦ ρ ⟧-ren η) ≡ ⟦ ρ ᵣ∘ₛ σ ⟧-sub η
        -- ⟦ σ ⟧-sub η ≡ ⟦ σ' ⟧-sub (η , x)
    sub-ren {Γ} {Γ'} {Contexts.[]} ρ σ η = refl
    sub-ren {Γ} {Γ'} {Γ'' Contexts.∷ x} ρ σ η = cong₂ _,_ 
        (sub-ren ρ ((λ x₁ → σ (there x₁))) η)
        {!  ρ ᵣ∘ₛ σ   !} --(sub-there (σ here) ρ η) 

    --sub-ren-value
    --sub-ren-user
    --sub-ren-kernel
    sub-ren-value : ∀ { Γ Γ' X} (V : Γ' ⊢V: X) (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ V ⟧-value (⟦ ρ ⟧-ren η) ≡ ⟦ V [ ρ ]ᵥᵣ ⟧-value η
    sub-ren-value {Γ} {Γ'} (var x) ρ η = abc x ρ η
    sub-ren-value {Γ} {Γ'} (sub-value V x) ρ η = cong (coerceᵥ x) (sub-ren-value V ρ η) 
    sub-ren-value {Γ} {Γ'} ⟨⟩ ρ η = refl
    sub-ren-value {Γ} {Γ'} ⟨ V , W ⟩ ρ η = cong₂ _,_ (sub-ren-value V ρ η) (sub-ren-value W ρ η) 
    sub-ren-value {Γ} {Γ'} (funU x) ρ η = fun-ext (λ X 
        → cong₂ (λ a b → a b) {x =  ⟦ funU x ⟧-value (⟦ ρ ⟧-ren η)} {y = ⟦ funU x [ ρ ]ᵥᵣ ⟧-value η} 
            (fun-ext (λ Y 
                → {!   !}))  
            refl)
    sub-ren-value {Γ} {Γ'} (funK x) ρ η = 
        begin 
        {!   !} 
        ≡⟨ {!   !} ⟩ 
        {!   !} 
        ≡⟨ {!   !} ⟩ 
        {!   !} 
        ∎
    sub-ren-value {Γ} {Γ'} (runner x) ρ η = {!   !}

    sub-ren-user : ∀ { Γ Γ' Xᵤ} (M : Γ' ⊢U: Xᵤ) (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ M ⟧-user (⟦ ρ ⟧-ren η) ≡ ⟦ M [ ρ ]ᵤᵣ ⟧-user η
    sub-ren-user {Γ} {Γ'} {Xᵤ} (sub-user M p) ρ η = {!   !}
    sub-ren-user {Γ} {Γ'} {Xᵤ} (return V) ρ η = cong leaf (sub-ren-value V ρ η)
    sub-ren-user {Γ} {Γ'} {Xᵤ} (V · W) ρ η = {!   !}
    sub-ren-user {Γ} {Γ'} {Xᵤ} (opᵤ op x par M) ρ η = {!   !}
    sub-ren-user {Γ} {Γ'} {Xᵤ} (`let M `in N) ρ η = {!   !}
    sub-ren-user {Γ} {Γ'} {Xᵤ} (match V `with M) ρ η = {!   !}
    sub-ren-user {Γ} {Γ'} {Xᵤ} (`using R at C `run M finally N) ρ η = {!   !}
    sub-ren-user {Γ} {Γ'} {Xᵤ} (kernel K at C finally M) ρ η = {!   !}

    sub-ren-kernel : ∀ { Γ Γ' Xₖ} (K : Γ' ⊢K: Xₖ) (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η) ≡ ⟦ K [ ρ ]ₖᵣ ⟧-kernel η
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (sub-kernel K p) ρ η = {!   !}
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (return V) ρ η = fun-ext (λ C → cong leaf (cong₂ _,_ (sub-ren-value V ρ η) refl))  
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (V · W) ρ η = {!    !}
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (`let K `in L) ρ η = {!   !}
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (match V `with K) ρ η = {!   !}
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (opₖ op x par K) ρ η = {!   !}
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (getenv K) ρ η = {!   !}
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (setenv V K) ρ η = {!   !}
    sub-ren-kernel {Γ} {Γ'} {Xₖ} (user M `with K) ρ η = {!   !}

    --lookup-ren
    abc : ∀ { Γ Γ' v} (x : v ∈ Γ') (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → lookup x (⟦ ρ ⟧-ren η) ≡ lookup (ρ x) η
    abc here ρ η = refl
    abc (there x) ρ η = abc x (λ x → ρ (there x)) η
    --TODO 11. 3. - RENAME THESE TO SENSIBLE NAMES
    -- Eq.trans right hand side use induction hypothesis then continue on like that.
    -- lookup x (⟦ ρ ∘ wkᵣ ⟧ ≡ 


    -- ρ ᵣ∘ₛ σ = λ x → σ x [ ρ ]ᵥᵣ
{-    sub-there : ∀ { Γ Γ' Γ'' v} (ρ : Ren Γ Γ') (σ : Sub Γ' (Γ'' ∷ v)) (η : ⟦ Γ ⟧-ctx)
        → ⟦ σ here ⟧-value (⟦ ρ ⟧-ren η) ≡ ⟦ (ρ ᵣ∘ₛ σ) here ⟧-value η
    sub-there {Γ} {Γ'} {Γ''} {v} ρ σ η = {!   !}-}

    sub-there' : ∀ { Γ Γ' Γ''} {X : VType} (ρ : Ren Γ Γ') (V : Γ' ⊢V: X)  (η : ⟦ Γ ⟧-ctx) --(η' : ⟦ Γ ⟧-ctx)
        → ⟦ V ⟧-value (⟦ ρ ⟧-ren η) ≡ ⟦ {! ρ   !} ⟧-value η
    sub-there' {Γ} {Γ'} {Γ''} ρ v η = {!   !}

--

    sub-V : ∀ { Γ Γ' X  } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (v : Γ' ⊢V: X)
        → ⟦ v ⟧-value (⟦ σ ⟧-sub η) ≡ ⟦ v [ σ ]ᵥ ⟧-value η
    sub-V {Γ' = Γ' ∷ X} σ η (var here) = refl
    sub-V {Γ' = Γ' ∷ X} σ η (var (there x)) = sub-V {Γ' = Γ'} (σ ∘ there) η (var x)
    sub-V σ η (sub-value v x) = cong (coerceᵥ x) ((sub-V σ η v))
    sub-V σ η ⟨⟩ = refl
    sub-V σ η ⟨ v , w ⟩ = cong₂ _,_ (sub-V σ η v) (sub-V σ η w)


    sub-V {Γ = Γ} {Γ' = Γ'} σ η (funU {X} m) = fun-ext (λ X' 
        → Eq.trans 
            (cong ⟦ m ⟧-user (cong₂ _,_ {!   !} refl))
            (sub-U (extendₛ σ) (η , X') m))
    --sub-V {Γ} {Γ' = []} σ η (Terms.funU {X} m) = fun-ext (λ X' → Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (Eq.trans refl refl) refl)) (sub-U (extendₛ σ) (η , X') m))
    --sub-V {Γ} {Γ' = Γ' ∷ x} σ η (Terms.funU {X} m) = fun-ext (λ X' → Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (cong₂ _,_ {!   !} {!   !}) refl)) (sub-U (extendₛ σ) (η , X') m))
    --sub-V {Γ = Γ ∷ x} {Γ' = Γ'} σ η (funU {X} m) = fun-ext (λ X' → Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (Eq.trans {!   !} {!   !}) refl)) (sub-U (extendₛ σ) (η , X') m))



    --POTENTIAL TODO 11. 3.: use begin_ syntactic sugar to make the proofs prettier. 

    sub-V σ η (funK k) = fun-ext (λ X → {! sub-K (extendₛ σ) (η , X) k  !}) 
    sub-V σ η (runner r) = {!   !}

    sub-U : ∀ { Γ Γ' Xᵤ  } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (m : Γ' ⊢U: Xᵤ)
        → ⟦ m ⟧-user (⟦ σ ⟧-sub η) ≡ ⟦ m [ σ ]ᵤ ⟧-user η
    sub-U σ η (sub-user m p) = cong (coerceᵤ p) (sub-U σ η m)
    sub-U σ η (return v) = cong leaf (sub-V σ η v) 
    sub-U σ η (v · w) = cong₂ (λ z → z) (sub-V σ η v) (sub-V σ η w) --ISSUE: How is (λ z → z) accepted?
    sub-U σ η (opᵤ op p par m) = cong₂ (node op p) (sub-V σ η par) (fun-ext (λ res → {! sub-U   !}))
    sub-U σ η (`let m `in n) = cong₂ bind-tree 
        (fun-ext (λ X 
            → Eq.trans 
                (cong ⟦ n ⟧-user (cong₂ _,_ 
                                    {!   !}
                                    refl))  
                (sub-U (extendₛ σ) (η , X) n) )) 
        (sub-U σ η m)
    sub-U σ η (match v `with m) = Eq.trans (cong ⟦ m ⟧-user {!   !}) 
        (sub-U (extendₛ (extendₛ σ)) ((η , proj₁ (⟦ v [ σ ]ᵥ ⟧-value η)) , proj₂ (⟦ v [ σ ]ᵥ ⟧-value η)) m)
    sub-U σ η (`using r at c `run m finally n) = {! cong₂  bind-tree ? ?   !}
    sub-U σ η (kernel k at c finally m) = {! begin  !}

    sub-K : ∀ { Γ Γ' Xₖ  } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (k : Γ' ⊢K: Xₖ)
        → (⟦ k ⟧-kernel (⟦ σ ⟧-sub η)) ≡ (⟦ k [ σ ]ₖ ⟧-kernel η) 
    sub-K σ η (sub-kernel k p) = cong (coerceₖ p) (sub-K σ η k) 
    sub-K σ η (return v) = fun-ext (λ C → cong leaf (cong₂ _,_ (sub-V σ η v) refl))
    sub-K σ η (v · w) = cong₂ (λ x y → x y) (sub-V σ η v) (sub-V σ η w)
    sub-K σ η (`let k `in l) = fun-ext (λ c → cong₂ bind-tree {! ((cong₂ (λ x C' → x C') ? refl))  !} (cong₂ (λ x y → x y) (sub-K σ η k) refl)) 
    --(cong₂ (λ x y → x y) {x = ?} {u = c} (fun-ext ?) refl)
    --⟦ `let k `in l ⟧-kernel (⟦ σ ⟧-sub η) c ≡
    --⟦ `let k `in l [ σ ]ₖ ⟧-kernel η c

    --(cong ⟦ k ⟧-kernel (cong₂ _,_ (cong₂ _,_ (Eq.trans (sub-weakening σ η) (sub-weakening (λ x → σ x [ there ]ᵥᵣ) (η , proj₁ (⟦ v [ σ ]ᵥ ⟧-value η)))) {! cong (λ x → proj₁ x)   !}) {!   !})) 
    sub-K σ η (match v `with k) = Eq.trans 
        (cong ⟦ k ⟧-kernel 
            (cong₂ _,_ 
                (cong₂ _,_
                    {!   !} 
                    --(Eq.trans 
                        --{! (sub-weakening σ η)  !} 
                        --{! (sub-weakening (λ x → σ x [ (λ x₁ → there x₁) ]ᵥᵣ) (η , proj₁ (⟦ v [ σ ]ᵥ ⟧-value η)))  !} )  
                    {! cong (λ x → proj₁ x)   !}) (cong proj₂ (sub-V σ η v)) )) 
                (sub-K (extendₛ (extendₛ σ)) ((η , proj₁ (⟦ v [ σ ]ᵥ ⟧-value η)) , proj₂ (⟦ v [ σ ]ᵥ ⟧-value η)) k)
    sub-K σ η (opₖ op p par k) = fun-ext 
        (λ C → cong₂ (node op p) 
            (sub-V σ η par) 
            (fun-ext 
                (λ res → cong₂ (λ k C → k C) {x = ⟦ k ⟧-kernel (⟦ σ ⟧-sub η , res)} {y = ⟦ k [ extendₛ σ ]ₖ ⟧-kernel (η , res)} 
                    (Eq.trans 
                        (cong ⟦ k ⟧-kernel (cong₂ _,_ {! (sub-weakening σ η)  !} refl))  
                        (sub-K (extendₛ σ) (η , res) k)) 
                    refl)))  
    sub-K σ η (getenv k) = fun-ext 
        (λ C → cong₂ (λ a b → a b) {x = ⟦ k ⟧-kernel (⟦ σ ⟧-sub η , C)} {y = ⟦ k [ extendₛ σ ]ₖ ⟧-kernel (η , C)} {u = C} {v = C} 
            (Eq.trans 
                (cong ⟦ k ⟧-kernel (cong₂ _,_ {! (sub-weakening σ η)  !} refl))  
                (sub-K (extendₛ σ) (η , C) k)) 
            refl) 
    sub-K σ η (setenv c k) = fun-ext (λ x → {! cong₂ (λ a b → a b) {x = ⟦ setenv c k ⟧-kernel} {y = ?} {u = (⟦ σ ⟧-sub η)} {v = (⟦ c [ σ ]ᵥ ⟧-value η)}  
        ? 
        ?  !})
    sub-K σ η (user m `with k) = fun-ext (λ C → 
        cong₂ bind-tree 
            (fun-ext (λ X → 
                cong₂ (λ a b → a b) {x = ⟦ k ⟧-kernel (⟦ σ ⟧-sub η , X)} {y = ⟦ k [ extendₛ σ ]ₖ ⟧-kernel (η , X)} 
                    (Eq.trans 
                        (cong ⟦ k ⟧-kernel 
                            (cong₂ _,_ 
                                {!   !} --(sub-weakening σ η)
                                refl))
                        (sub-K (extendₛ σ) (η , X) k)) 
                    refl)) 
            (sub-U σ η m)) 
          
              