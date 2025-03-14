--{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Unit
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using ( _≡⟨⟩_ ; _∎ ) renaming (begin_ to start_ ; step-≡ to step-= ) 
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
import Sub-Validity

module Validity (G : GTypes) (O : Ops G) where

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
open Sub-Validity G O
 
mutual

    valid-V : ∀ {Γ : Ctx} {X : VType} {v w : Γ ⊢V: X} → (Γ ⊢V v ≡ w) → ∀ η → ⟦ v ⟧-value η ≡ ⟦ w ⟧-value η
    valid-U : ∀ {Γ : Ctx} {Xᵤ : UType} {m n : Γ ⊢U: Xᵤ} → (Γ ⊢U m ≡ n) → ∀ η → ⟦ m ⟧-user η ≡ ⟦ n ⟧-user η
    valid-K : ∀ {Γ : Ctx} {Xₖ : KType} {k l : Γ ⊢K: Xₖ} → (Γ ⊢K k ≡ l) → ∀ η → ⟦ k ⟧-kernel η ≡ ⟦ l ⟧-kernel η

    valid-V refl η = Eq.refl
    valid-V (sym eq-v) η = Eq.sym (valid-V eq-v η)
    valid-V (trans eq-v eq-w) η = Eq.trans (valid-V eq-v η) (valid-V eq-w η)
    valid-V (prod-cong eq-v eq-w) η = Eq.cong₂ _,_ (valid-V eq-v η) (valid-V eq-w η)
    valid-V (fun-cong eq-m) η = fun-ext (λ x → valid-U eq-m (η , x)) --fun-ext (λ x → valid-U eq (η , x))
    valid-V (funK-cong eq-k) η = fun-ext (λ x → valid-K eq-k (η , x))  --fun-ext (λ x → valid-K refl η) 
    valid-V (runner-cong eq-k) η = fun-ext (λ op → fun-ext (λ p → fun-ext (λ param → valid-K (eq-k op p) (η , param)))) --fun-ext (λ op → fun-ext (λ p → fun-ext (λ param → valid-K refl η)))
    valid-V unit-eta η = refl
    valid-V {w = w} funU-eta η = 
        Eq.trans 
            (fun-ext (λ x 
                -- ⟦ w [ (λ x₁ → there x₁) ]ᵥᵣ ⟧-value (η , x) x ≡ _j_133 x
                → cong₂ (λ a b → a b) {x = ⟦ w [ (λ x₁ → there x₁) ]ᵥᵣ ⟧-value (η , x)} {u = x}
                    {!   !} 
                    refl)) 
            (fun-ext (λ x 
                -- ⟦ w ⟧-value η
                → cong₂ (λ a b → a b) {y = ⟦ w ⟧-value η} {u = x} 
                    {!   !} 
                    refl ))   --Relies on substitution (complete mystery for now)
    valid-V {w = w} funK-eta η = 
        Eq.trans 
            (fun-ext (λ X 
                → cong₂ (λ a b → a b) {x = ⟦ w [ (λ x₁ → there x₁) ]ᵥᵣ ⟧-value (η , X)} 
                    {!   !} 
                    refl))
            {!   !} 
            
            --fun-ext (λ x → valid-K refl η) --Relies on substitution (complete mystery for now)




    valid-U refl η = Eq.refl
    valid-U (sym eq-m) η = Eq.sym (valid-U eq-m η) 
    valid-U (trans eq-m eq-n) η = Eq.trans (valid-U eq-m η) (valid-U eq-n η) 
    valid-U (return-cong eq-v) η = Eq.cong (λ x → leaf x) (valid-V eq-v η)
    valid-U {Γ} {Xᵤ} {m} {n} (·-cong eq-v eq-w) η = cong₂ (λ v-value w-value → v-value w-value) (valid-V eq-v η) (valid-V eq-w η)
    valid-U (opᵤ-cong p eq-v eq-m) η = cong₂ (node _ p) (valid-V eq-v η) (fun-ext (λ res → valid-U eq-m (η , res))) 
    valid-U (let-in-cong eq-m eq-n) η = cong₂ bind-user (fun-ext (λ x → valid-U eq-n (η , x))) (valid-U eq-m η)
    valid-U (match-with-cong eq-v eq-m) η = cong₂ (λ m η' → m η') (fun-ext (λ η' → valid-U eq-m η')) (cong (λ x → ( η , proj₁ x) , proj₂ x) (valid-V eq-v η))
    valid-U (using-at-run-finally-cong eq-r eq-w eq-m eq-n) η = 
        cong₂ bind-tree (fun-ext (λ η' → valid-U eq-n ((η , proj₁ η') , proj₂ η') ))  
            (cong₂ (λ r,m w → apply-runner (proj₁ r,m) (proj₂ r,m) w)  (cong₂ (λ r m → r , m)  (valid-V eq-r η) (valid-U eq-m η)) (valid-V eq-w η))
    valid-U (kernel-at-finally-cong eq-v eq-m eq-k) η = 
        cong₂ bind-tree (fun-ext (λ x → valid-U eq-m ((η , proj₁ x) , proj₂ x))) (cong₂ (λ k c → k c ) (valid-K eq-k η) (valid-V eq-v η))


    valid-U (funU-beta m v) η = Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ sub-var refl)) (sub-U (var ∷ₛ v) η m) --Relies on substitution (complete mystery for now)



    valid-U (let-in-beta-return_ v m) η = Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ sub-var refl)) (sub-U (var ∷ₛ v) η m) --Relies on substitution (complete mystery for now)


    valid-U (let-in-beta-op op p param m n) η = cong (node op p (⟦ param ⟧-value η)) 
        (fun-ext 
        (λ res → cong₂ bind-tree (fun-ext (λ x₁ → Eq.trans (cong ⟦ n ⟧-user (cong₂ _,_ {!   !} refl)) (sub-U (extendₛ (λ p₁ → var (there p₁))) ((η , res) , x₁) n))) refl))
        --cong (node op p (⟦ param ⟧-value η)) (fun-ext (λ res → cong₂ bind-tree (fun-ext (λ X₁ → {!   !})) refl)) --Relies on substitution (complete mystery for now)
        

    valid-U (match-with-beta-prod v w m) η = Eq.trans {!    !} (sub-U ((var ∷ₛ v) ∷ₛ w) η m) --Relies on substitution (complete mystery for now)
        --ALMOST COMPLETED


    valid-U (using-run-finally-beta-return r w v m) η = Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (cong₂ _,_ sub-var refl) refl))
        (sub-U ((var ∷ₛ v) ∷ₛ w) η m) --Relies on substitution (complete mystery for now)
    {-
    ⟦ m ⟧-user ((η , ⟦ v ⟧-value η) , ⟦ w ⟧-value η) ≡
        ⟦ m [ (var ∷ₛ v) ∷ₛ w ]ᵤ ⟧-user η
        This repeated between the previous two examples
    ⟦ m ⟧-user ((η , ⟦ v ⟧-value η) , ⟦ w ⟧-value η) ≡
        ⟦ m [ (var ∷ₛ v) ∷ₛ w ]ᵤ ⟧-user η
    -}

    valid-U (using-run-finally-beta-op R w op param p m n) η = {! cong₂ bind-tree ? (cong₂ bind-tree ? (Eq.trans ? (sub-U )   !} --Relies on substitution (complete mystery for now)
    valid-U (kernel-at-finally-beta-return v c n) η = Eq.trans (cong ⟦ n ⟧-user {!   !}) (sub-U ((var ∷ₛ v) ∷ₛ c) η n) --Relies on substitution (complete mystery for now)
    valid-U (kernel-at-finally-beta-getenv c k m) η = {! cong (bind-tree _) (sub-K )  !} --Relies on substitution (complete mystery for now)
    valid-U (kernel-at-finally-setenv c c' k m) η = {!   !} --refl --Strange
    valid-U (kernel-at-finally-beta-op op p param c k m) η = {!  !} --Relies on substitution (complete mystery for now)

    valid-U (let-in-eta-M n) η = {!   !} 
        --Eq.cong-app refl (⟦ n ⟧-user η) 
        --bind-tree (λ X₁ → leaf X₁) (⟦ n ⟧-user η) ≡ ⟦ n ⟧-user η

    valid-K refl η = Eq.refl
    valid-K (sym eq-k) η = Eq.sym (valid-K eq-k η)
    valid-K (trans eq-k eq-l) η = Eq.trans (valid-K eq-k η) (valid-K eq-l η) 
    valid-K (return-cong eq-v) η = fun-ext (λ x → cong leaf (cong (λ y → (y , x)) (valid-V eq-v η))) 
    valid-K (·-cong eq-v eq-w) η = cong₂ (λ v-value w-value → v-value w-value) (valid-V eq-v η) (valid-V eq-w η) 
    valid-K (let-in-cong eq-k eq-l) η = 
        fun-ext (λ c → cong₂ bind-tree (fun-ext (λ x → cong (λ x₁ → x₁ (proj₂ x)) (valid-K eq-l (η , proj₁ x) )) )  (cong₂ (λ a b → a b) (valid-K eq-k η) refl) )
    valid-K (match-with-cong eq-v eq-k) η = cong₂ (λ k v → k v) (fun-ext (λ η' → valid-K eq-k η' )) (cong (λ v → (( η , proj₁ v ) , proj₂ v)) (valid-V eq-v η))
    valid-K (opₖ-cong {V} {W} {Σ} {C} {op} {p} {param} eq-v eq-k) η = fun-ext (λ _ → cong₂ (node op p) (valid-V eq-v η) (fun-ext (λ res → cong₂ (λ k≡k' c → k≡k' c) (valid-K eq-k (η , res))  refl ))) 
    --TODO 28. 01. : change the names of these variables to be appropriate to what they represent
    valid-K (getenv-cong eq-k) η = fun-ext (λ c → cong₂ (λ k≡k' c' → k≡k' c') (valid-K eq-k (η , c)) refl)
    --TODO 28. 01. : change the names of these variables to be appropriate to what they represent
    valid-K (setenv-cong eq-v eq-k) η = fun-ext (λ _ → cong₂ (λ k c → k c) (valid-K eq-k η) (valid-V eq-v η)) 
    valid-K (user-with-cong eq-m eq-k) η = fun-ext (λ _ → cong₂ bind-tree (cong₂ (λ f c x → f x c) (fun-ext (λ x → valid-K eq-k (η , x) ))  refl) (valid-U eq-m η))  
            
    valid-K (funK-beta k v) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (let-in-beta-return v k) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (let-in-beta-op op p param k l) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (let-in-beta-getenv k l) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (let-in-beta-setenv c k l) η = refl 
    valid-K (match-with-beta-prod v w k) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (user-with-beta-return v k) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (user-with-beta-op op p param m k) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (let-in-eta-K l) η = fun-ext (λ x → cong₂ (λ x₁ x₂ → x₁ x₂) refl refl) 
        --Eq.cong-app refl (⟦ l ⟧-kernel η _) 
    {-(λ C₁ →
            bind-tree (λ { (x , C') → leaf (x , C') }) (⟦ l ⟧-kernel η C₁))
        ≡ ⟦ l ⟧-kernel η-}
    valid-K (GetSetenv _ v) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (SetGetenv c k) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (SetSetenv c c' k) η = fun-ext (λ c'' → refl)
    valid-K (GetOpEnv op p param k) η = {!  !} --Relies on substitution (complete mystery for now)
    valid-K (SetOpEnv op p param _) η = {!  !} --Relies on substitution (complete mystery for now)
 