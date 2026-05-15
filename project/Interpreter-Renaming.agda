open import Data.Unit
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning     

open import Function

import Contexts
open import Parameters

module Interpreter-Renaming (G : GTypes) (O : Ops G) where

open GTypes G
open Ops O

open Contexts G O
open import Types G O
open import Terms G O
open import Interpreter G O 
open import Renaming G O 
open import Substitution G O
open import Trees G O


{-ren-coop-lemma : ∀ { Γ Γ' Σ C op} (ρ : Ren Γ Γ') (coop : co-op Γ' Σ C op)
    → coop [ extdᵣ ρ ]ₖᵣ ≡ {!   !}
ren-coop-lemma ρ (sub-kernel coop _) = refl
ren-coop-lemma ρ (return _) = refl
ren-coop-lemma ρ (_ · _) = refl
ren-coop-lemma ρ (`let coop `in coop') = refl
ren-coop-lemma ρ (match _ `with coop) = refl
ren-coop-lemma ρ (opₖ op' _ _ coop) = refl
ren-coop-lemma ρ (getenv coop) = refl
ren-coop-lemma ρ (setenv _ coop) = refl
ren-coop-lemma ρ (user _ `with coop) = refl-}

mutual 

    ⟦_⟧-ren : ∀ {Γ Γ'} → Ren Γ Γ' → ⟦ Γ ⟧-ctx → ⟦ Γ' ⟧-ctx
    ⟦_⟧-ren {Γ' = []} ρ η = tt
    ⟦_⟧-ren {Γ' = Γ' ∷ X} ρ η = ⟦ ρ ∘ there ⟧-ren η , lookup (ρ here) η

    ren-wk : ∀ {Γ Γ' X} {V : ⟦ X ⟧v} (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx) 
        → ⟦ ρ ⟧-ren η ≡ ⟦ ρ ∘ᵣ there {Y = X} ⟧-ren (η , V)
    ren-wk {Γ} {[]} ρ η = refl
    ren-wk {Γ} {Γ' ∷ X} ρ η = cong₂ _,_ 
        (ren-wk (there ∘ᵣ ρ) η) 
        refl

    ren-id-lemma : ∀ {Γ} (η : ⟦ Γ ⟧-ctx)
        → η ≡ ⟦ idᵣ ⟧-ren η
    ren-id-lemma {[]} η = refl
    ren-id-lemma {Γ ∷ X} (η , V) = cong₂ _,_ 
        (begin 
        η 
        ≡⟨ ren-id-lemma η ⟩ 
        ⟦ idᵣ ⟧-ren η 
        ≡⟨ ren-wk idᵣ η ⟩
        ⟦ there {Y = X} ⟧-ren (η , V) 
        ∎) 
        refl

    --lookup-ren
    lookup-ren : ∀ { Γ Γ' V} (x : V ∈ Γ') (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → lookup x (⟦ ρ ⟧-ren η) ≡ lookup (ρ x) η
    lookup-ren here ρ η = refl
    lookup-ren (there x) ρ η = lookup-ren x (λ x → ρ (there x)) η

    ren-value : ∀ { Γ Γ' X} (V : Γ' ⊢V: X) (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ V ⟧-value (⟦ ρ ⟧-ren η) ≡ ⟦ V [ ρ ]ᵥᵣ ⟧-value η
    ren-value {Γ} {Γ'} (var x) ρ η = lookup-ren x ρ η
    ren-value {Γ} {Γ'} (sub-value V p) ρ η = cong (coerceᵥ p) 
        (ren-value V ρ η) 
    ren-value {Γ} {Γ'} ⟨⟩ ρ η = refl
    ren-value {Γ} {Γ'} ⟨ V , W ⟩ ρ η = cong₂ _,_ 
        (ren-value V ρ η) 
        (ren-value W ρ η) 
    ren-value {Γ} {Γ'} (funU M) ρ η = fun-ext (λ X 
        → cong₂ (λ a b → a b) 
        {x = ⟦ funU M ⟧-value (⟦ ρ ⟧-ren η)} 
        {y = ⟦ funU M [ ρ ]ᵥᵣ ⟧-value η} 
            (fun-ext (λ Y → 
                Eq.trans 
                    (cong ⟦ M ⟧-user (cong₂ _,_ 
                        (ren-wk {V = Y} ρ η)
                        refl))
                    (ren-user M (extdᵣ ρ) (η , Y))))  
            refl)
    ren-value {Γ} {Γ'} (funK K) ρ η = fun-ext (λ X → 
        Eq.trans 
            (cong ⟦ K ⟧-kernel (cong₂ _,_ 
                (ren-wk {V = X} ρ η)
                refl)) 
            (ren-kernel K (extdᵣ ρ) (η , X)))
    ren-value {Γ} {Γ'} {Σ ⇒ Σ' , C} (runner {Σ} {Σ'} {C} R) ρ η = 
        fun-ext (λ op → fun-ext (λ x' → fun-ext (λ par → 
        begin 
        ⟦ R op x' ⟧-kernel (⟦ ρ ⟧-ren η , par) 
        ≡⟨ cong ⟦ R op x' ⟧-kernel (cong₂ _,_ 
            (ren-wk ρ η)
            refl) ⟩ 
        ⟦ R op x' ⟧-kernel 
            (⟦ extdᵣ {Γ'} {Γ} {X = gnd (param op)} ρ ⟧-ren (η , par)) 
        ≡⟨ (ren-kernel (R op x') (extdᵣ ρ) (η , par)) ⟩ 
        ⟦ R op x' [ extdᵣ ρ ]ₖᵣ ⟧-kernel (η , par) 
        ≡⟨ cong₂ (λ a b → a b) 
                {x = ⟦ R op x' [ extdᵣ ρ ]ₖᵣ ⟧-kernel}
                {y = ⟦ R op x' [ extdᵣ ρ ]ₖᵣ ⟧-kernel}
                {u = η , par}
                {v = η , par}
                (cong ⟦_⟧-kernel 
                    {x = R op x' [ extdᵣ ρ ]ₖᵣ} 
                    {y = R op x' [ extdᵣ ρ ]ₖᵣ} 
                    refl)
                refl ⟩ 
        refl)))

    ren-user : ∀ { Γ Γ' Xᵤ} (M : Γ' ⊢U: Xᵤ) (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ M ⟧-user (⟦ ρ ⟧-ren η) ≡ ⟦ M [ ρ ]ᵤᵣ ⟧-user η
    ren-user {Γ} {Γ'} {Xᵤ} (sub-user M p) ρ η = 
        cong (coerceᵤ p) (ren-user M ρ η) 
    ren-user {Γ} {Γ'} {Xᵤ} (return V) ρ η = cong leaf (ren-value V ρ η)
    ren-user {Γ} {Γ'} {Xᵤ} (V · W) ρ η = cong₂ (λ a b → a b) 
        (ren-value V ρ η) 
        (ren-value W ρ η) 
    ren-user {Γ} {Γ'} {Xᵤ} (opᵤ op x par M) ρ η = cong₂ (node op x) 
        (ren-value par ρ η) 
        (fun-ext (λ res → Eq.trans 
                (cong ⟦ M ⟧-user (cong₂ _,_
                    (ren-wk {V = res} ρ η)
                    refl))
                (ren-user M (extdᵣ ρ) (η , res)))) 
    ren-user {Γ} {Γ'} {Xᵤ} (`let M `in N) ρ η = cong₂ bind-tree 
        (fun-ext (λ X → Eq.trans
            (cong ⟦ N ⟧-user (cong₂ _,_
                (ren-wk {V = X} ρ η)
                refl))
            (ren-user N (extdᵣ ρ) (η , X)))) 
        (ren-user M ρ η)
    ren-user {Γ} {Γ'} {X ! Σ} (match_`with {X'} {Y'} {X ! Σ} V M) ρ η = 
        begin 
        (⟦ M ⟧-user ((⟦ ρ ⟧-ren η , proj₁ (⟦ V ⟧-value (⟦ ρ ⟧-ren η))) , proj₂ (⟦ V ⟧-value (⟦ ρ ⟧-ren η)))
        ≡⟨ cong ⟦ M ⟧-user (cong₂ _,_ 
            {v = proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)} 
            (cong₂ _,_ 
                refl
                (cong proj₁ (ren-value V ρ η)))
            (cong proj₂ (ren-value V ρ η))) ⟩
        ⟦ M ⟧-user
          ((⟦ ρ ⟧-ren η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) ,
           proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η))
        ≡⟨ cong ⟦ M ⟧-user (cong₂ _,_ 
            (cong₂ _,_ 
                (Eq.trans 
                    (ren-wk ρ η)
                    (ren-wk (ρ ∘ᵣ there) (η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)))) 
                refl) 
            refl) ⟩
        ⟦ M ⟧-user (⟦ extdᵣ {X = Y'} (extdᵣ {Γ'} {Γ} {X'} ρ) ⟧-ren 
            ((η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)))
        ≡⟨ ren-user M (extdᵣ (extdᵣ ρ)) ((η , (proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η))) , (proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η))) ⟩ 
        refl)
    ren-user {Γ} {Γ'} {Xᵤ} (`using_at_`run_finally {Σ} {Σ'} {C'} {X'} {Y'} R C M N) ρ η = cong₂ bind-tree
        {x = (λ { (x , c') → ⟦ N ⟧-user ((⟦ ρ ⟧-ren η , x) , c') })}
        {y = λ { (x , c') → ⟦ N [ extdᵣ (extdᵣ ρ) ]ᵤᵣ ⟧-user ((η , x) , c')}}
        {u = (apply-runner (⟦ R ⟧-value (⟦ ρ ⟧-ren η)) (⟦ M ⟧-user (⟦ ρ ⟧-ren η)) (⟦ C ⟧-value (⟦ ρ ⟧-ren η)))}
        {v = (apply-runner (⟦ R [ ρ ]ᵥᵣ ⟧-value η) (⟦ M [ ρ ]ᵤᵣ ⟧-user η) (⟦ C [ ρ ]ᵥᵣ ⟧-value η))}
        (fun-ext (λ {(x , c') → 
            begin 
                (⟦ N ⟧-user ((⟦ ρ ⟧-ren η , x) , c') 
                ≡⟨ cong ⟦ N ⟧-user (cong₂ _,_ 
                    (cong₂ _,_ 
                        (Eq.trans 
                            (ren-wk ρ η)
                            (ren-wk (ρ ∘ᵣ there) (η , x)))
                        refl) 
                    refl) ⟩ 
                ⟦ N ⟧-user (⟦ extdᵣ {X = gnd C'} (extdᵣ {X = X'} ρ) ⟧-ren ((η , x) , c'))
                ≡⟨ ren-user N (extdᵣ (extdᵣ ρ)) ((η , x) , c') ⟩ 
                refl)}))
        (begin 
            apply-runner (⟦ R ⟧-value (⟦ ρ ⟧-ren η)) (⟦ M ⟧-user (⟦ ρ ⟧-ren η)) (⟦ C ⟧-value (⟦ ρ ⟧-ren η)) 
            ≡⟨ cong (apply-runner (⟦ R ⟧-value (⟦ ρ ⟧-ren η)) (⟦ M ⟧-user (⟦ ρ ⟧-ren η))) (ren-value C ρ η) ⟩ 
            apply-runner (⟦ R ⟧-value (⟦ ρ ⟧-ren η)) (⟦ M ⟧-user (⟦ ρ ⟧-ren η)) (⟦ C [ ρ ]ᵥᵣ ⟧-value η) 
            ≡⟨ cong₂ (λ a b → apply-runner a b (⟦ C [ ρ ]ᵥᵣ ⟧-value η)) 
                {x = (⟦ R ⟧-value (⟦ ρ ⟧-ren η))}
                {y = (⟦ R [ ρ ]ᵥᵣ ⟧-value η)}
                {u = (⟦ M ⟧-user (⟦ ρ ⟧-ren η))}
                {v = (⟦ M [ ρ ]ᵤᵣ ⟧-user η)}
                (ren-value R ρ η) 
                (ren-user M ρ η) ⟩ 
            apply-runner (⟦ R [ ρ ]ᵥᵣ ⟧-value η) (⟦ M [ ρ ]ᵤᵣ ⟧-user η) (⟦ C [ ρ ]ᵥᵣ ⟧-value η) 
        ∎)

    ren-user {Γ} {Γ'} {Xᵤ} (kernel_at_finally {X'} {Y'} {Σ'} {C'} K C M) ρ η = cong₂ bind-tree 
        {x = (λ { (X , C) → ⟦ M ⟧-user ((⟦ ρ ⟧-ren η , X) , C) })}
        {y = (λ { (X , C) → ⟦ M [ extdᵣ (extdᵣ ρ) ]ᵤᵣ ⟧-user ((η , X) , C)})}
        {u = (⟦ K ⟧-kernel (⟦ ρ ⟧-ren η) (⟦ C ⟧-value (⟦ ρ ⟧-ren η)))}
        {v = (⟦ K [ ρ ]ₖᵣ ⟧-kernel η (⟦ C [ ρ ]ᵥᵣ ⟧-value η))}
        (fun-ext (λ (X , C) → 
            begin
            ⟦ M ⟧-user ((⟦ ρ ⟧-ren η , X) , C) 
            ≡⟨ cong ⟦ M ⟧-user (cong₂ _,_ 
                (cong₂ _,_ 
                    (Eq.trans 
                        (ren-wk ρ η)
                        (ren-wk (ρ ∘ᵣ there) (η , X)))
                    refl) 
                refl) ⟩ 
            ⟦ M ⟧-user (⟦ extdᵣ {X = gnd C'} (extdᵣ {X = X'} ρ) ⟧-ren ((η , X) , C)) 
            ≡⟨ ren-user M (extdᵣ (extdᵣ ρ)) ((η , X) , C) ⟩ 
            refl 
        ))
        (cong₂ (λ a b → a b) 
            (ren-kernel K ρ η) 
            (ren-value C ρ η)) 


    ren-kernel : ∀ { Γ Γ' Xₖ} (K : Γ' ⊢K: Xₖ) (ρ : Ren Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η) ≡ ⟦ K [ ρ ]ₖᵣ ⟧-kernel η
    ren-kernel {Γ} {Γ'} {Xₖ} (sub-kernel K p) ρ η = cong (coerceₖ p) (ren-kernel K ρ η)
    ren-kernel {Γ} {Γ'} {Xₖ} (return V) ρ η = fun-ext (λ C → cong leaf (cong₂ _,_ (ren-value V ρ η) refl))  
    ren-kernel {Γ} {Γ'} {Xₖ} (var x · W) ρ η = cong₂ (λ a b → a b) 
        {x = lookup x (⟦ ρ ⟧-ren η)}{y = lookup (ρ x) η} 
        {u = ⟦ W ⟧-value (⟦ ρ ⟧-ren η)}{v = ⟦ W [ ρ ]ᵥᵣ ⟧-value η} 
        (lookup-ren x ρ η) 
        (ren-value W ρ η) 
    ren-kernel {Γ} {Γ'} {Xₖ} (sub-value V x · W) ρ η = cong₂ (λ a b → a b) 
        {x = coerceᵥ x (⟦ V ⟧-value (⟦ ρ ⟧-ren η))}{y = coerceᵥ x (⟦ V [ ρ ]ᵥᵣ ⟧-value η)}
        {u = ⟦ W ⟧-value (⟦ ρ ⟧-ren η)} {v = ⟦ W [ ρ ]ᵥᵣ ⟧-value η} 
        (cong (coerceᵥ x) (ren-value V ρ η)) 
        (ren-value W ρ η) 
    ren-kernel {Γ} {Γ'} {X ↯ Σ , C} (_·_ {X'} (funK K) W) ρ η = 
        begin 
        (⟦ K ⟧-kernel (⟦ ρ ⟧-ren η , ⟦ W ⟧-value (⟦ ρ ⟧-ren η)) 
        ≡⟨ cong ⟦ K ⟧-kernel (cong₂ _,_ 
            (ren-wk ρ η)
            (ren-value W ρ η) ) ⟩ 
        ⟦ K ⟧-kernel (⟦ extdᵣ {X = X'} ρ ⟧-ren (η , ⟦ W [ ρ ]ᵥᵣ ⟧-value η))
        ≡⟨ refl ⟩ 
        ⟦ K ⟧-kernel (⟦ extdᵣ {X = X'} ρ ⟧-ren (η , ⟦ W [ ρ ]ᵥᵣ ⟧-value η)) 
        ≡⟨ ren-kernel K (extdᵣ ρ) (η , ⟦ W [ ρ ]ᵥᵣ ⟧-value η) ⟩ 
        refl)
    ren-kernel {Γ} {Γ'} {Xₖ} (`let_`in {X'} {Y'} K L) ρ η = fun-ext (λ C → cong₂ bind-tree
        {x = (λ { (x , C') → ⟦ L ⟧-kernel (⟦ ρ ⟧-ren η , x) C' })}
        {y = (λ { (x , C') → ⟦ L [ extdᵣ ρ ]ₖᵣ ⟧-kernel (η , x) C' })}
        {u = (⟦ K ⟧-kernel (⟦ ρ ⟧-ren η) C)}
        {v = (⟦ K [ ρ ]ₖᵣ ⟧-kernel η C)}
        (fun-ext (λ (x' , C') → 
           begin 
            ⟦ L ⟧-kernel (⟦ ρ ⟧-ren η , x') C' 
            ≡⟨ cong (λ a → ⟦ L ⟧-kernel a C') (cong₂ _,_ 
                (ren-wk ρ η) 
                refl) ⟩ 
            ⟦ L ⟧-kernel (⟦ extdᵣ {X = X'} ρ ⟧-ren (η , x')) C' 
            ≡⟨ cong₂ (λ a b → a b) 
                (ren-kernel L (extdᵣ ρ) (η , x')) 
                refl ⟩ 
            (⟦ L [ extdᵣ ρ ]ₖᵣ ⟧-kernel (η , x') C') 
            ≡⟨ refl ⟩ 
            refl 
            ))
        (cong₂ (λ a b → a b) (ren-kernel K ρ η) refl))
    ren-kernel {Γ} {Γ'} {Xₖ} (match_`with {X'} {Y'} V K) ρ η = 
        begin 
        (⟦ K ⟧-kernel ((⟦ ρ ⟧-ren η , proj₁ (⟦ V ⟧-value (⟦ ρ ⟧-ren η))) , proj₂ (⟦ V ⟧-value (⟦ ρ ⟧-ren η))) 
        ≡⟨ cong ⟦ K ⟧-kernel (cong₂ _,_
            (cong₂ _,_ 
                refl 
                (cong proj₁ (ren-value V ρ η)))
            (cong proj₂ (ren-value V ρ η))) ⟩ 
        ⟦ K ⟧-kernel (((⟦ ρ ⟧-ren η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η))) 
        ≡⟨ cong ⟦ K ⟧-kernel (cong₂ _,_ 
            (cong₂ _,_ 
                (Eq.trans
                    (ren-wk ρ η)
                    (ren-wk (ρ ∘ᵣ there) (η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)))) 
                refl) 
            refl) ⟩
        ⟦ K ⟧-kernel (⟦ extdᵣ {X = Y'} 
            (extdᵣ {X = X'} ρ) ⟧-ren 
            ((η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)))  
        ≡⟨ ren-kernel K (extdᵣ (extdᵣ ρ)) ((η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) ⟩ 
        ⟦ K [ extdᵣ (extdᵣ ρ) ]ₖᵣ ⟧-kernel ((η , proj₁ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) , proj₂ (⟦ V [ ρ ]ᵥᵣ ⟧-value η)) 
        ≡⟨ refl ⟩ 
        refl)
    ren-kernel {Γ} {Γ'} {Xₖ} (opₖ op x par K) ρ η = fun-ext (λ C → 
        cong₂ (node op x) 
            (ren-value par ρ η) 
            (fun-ext (λ res → cong₂ (λ a b → a b)
                {x = ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η , res)}
                {y = ⟦ K [ extdᵣ ρ ]ₖᵣ ⟧-kernel (η , res)}
                (Eq.trans 
                    (cong ⟦ K ⟧-kernel (cong₂ _,_
                        (ren-wk ρ η)
                        refl)) 
                    (ren-kernel K (extdᵣ ρ) (η , res))) 
                refl)))
    ren-kernel {Γ} {Γ'} {Xₖ} (getenv K) ρ η = fun-ext (λ C → 
        cong₂ (λ a b → a b) 
            {x = ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η , C)}
            {y = ⟦ K [ extdᵣ ρ ]ₖᵣ ⟧-kernel (η , C)}
            (Eq.trans 
                (cong ⟦ K ⟧-kernel (cong₂ _,_ 
                    (ren-wk ρ η)
                    refl))
                (ren-kernel K (extdᵣ ρ) (η , C))) 
            refl)
    ren-kernel {Γ} {Γ'} {Xₖ} (setenv V K) ρ η = fun-ext (λ _ → 
        cong₂ (λ a b → a b) 
        {x = ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η)}
        {y = ⟦ K [ ρ ]ₖᵣ ⟧-kernel η} 
        (ren-kernel K ρ η) 
        (ren-value V ρ η))
    ren-kernel {Γ} {Γ'} {Xₖ} (user M `with K) ρ η = fun-ext (λ C → 
        cong₂ bind-tree
            {u = (⟦ M ⟧-user (⟦ ρ ⟧-ren η))}
            {v = (⟦ M [ ρ ]ᵤᵣ ⟧-user η)}
            (fun-ext λ X' → cong₂ (λ a b → a b)
                {x = ⟦ K ⟧-kernel (⟦ ρ ⟧-ren η , X')}
                {y = ⟦ K [ extdᵣ ρ ]ₖᵣ ⟧-kernel (η , X')}
                (Eq.trans
                    (cong ⟦ K ⟧-kernel (cong₂ _,_
                        (ren-wk ρ η)
                        refl))
                    (ren-kernel K (extdᵣ ρ) (η , X')))
                refl)
            (ren-user M ρ η))
