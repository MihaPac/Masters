open import Data.Unit
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning

open import Function

import Contexts
open import Parameters

module Interpreter-Substitution (G : GTypes) (O : Ops G) where

open GTypes G
open Ops O

open Contexts G O
open import Types G O
open import Terms G O
open import Interpreter G O 
open import Renaming G O 
open import Substitution G O
open import Interpreter-Renaming G O
open import Trees G O 

sub-coop-lemma : ∀ { Γ Γ' Σ C op } (σ : Sub Γ Γ') (coop : co-op Γ' Σ C op)
    → coop [ extendₛ σ ]ₖ  ≡ sub-coop coop σ
sub-coop-lemma σ (sub-kernel coop _) = refl
sub-coop-lemma σ (return _) = refl
sub-coop-lemma σ (_ · _) = refl
sub-coop-lemma σ (`let coop `in coop') = refl
sub-coop-lemma σ (match _ `with coop) = refl
sub-coop-lemma σ (opₖ op' _ _ coop) = refl
sub-coop-lemma σ (getenv coop) = refl
sub-coop-lemma σ (setenv _ coop) = refl
sub-coop-lemma σ (user _ `with coop) = refl


mutual
-- Naming scheme for the various equalities:
--   Γ ⊢V V ≡ W will be named eq-V, eq-W, ...
--   Γ ⊢U M ≡ N will be named eq-M, eq-N, ...
--   Γ ⊢K K ≡ L will be named eq-K, eq-L, ...
-- This naming scheme will be to quickly show the type of equivalence.

    ⟦_⟧-sub : ∀ {Γ Γ'} → Sub Γ Γ' → ⟦ Γ ⟧-ctx → ⟦ Γ' ⟧-ctx  
    ⟦_⟧-sub {Γ' = []} σ η = tt
    ⟦_⟧-sub {Γ' = Γ' ∷ X} σ η = (⟦ σ ∘ there ⟧-sub η) , ⟦ σ here ⟧-value η
        
    sub-wk : ∀ {Γ Γ' X} {V : ⟦ X ⟧v} (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx)
        → ⟦ σ ⟧-sub η ≡ ⟦ (λ x → σ x [ (λ y → there {Y = X} y) ]ᵥᵣ) ⟧-sub (η , V)
    sub-wk {Γ} {[]} σ η = refl
    sub-wk {Γ} {Γ' ∷ X'} {V = V} σ η = cong₂ _,_ 
        (sub-wk (σ ₛ∘ᵣ there) η)
        (begin 
        ⟦ σ here ⟧-value η 
        ≡⟨ cong ⟦ σ here ⟧-value (Eq.trans (ren-id-lemma η) (ren-wk idᵣ η)) ⟩ 
        ⟦ σ here ⟧-value (⟦ there ⟧-ren (η , V))
        ≡⟨ ren-value (σ here) there (η , _) ⟩ 
        refl)

    sub-id-lemma : ∀ { Γ } (η : ⟦ Γ ⟧-ctx)
        → η ≡ ⟦ (λ x → var x) ⟧-sub η
    sub-id-lemma {Contexts.[]} η = refl
    sub-id-lemma {Γ Contexts.∷ X} (η , V) = cong (_, V) 
        (begin 
        η 
        ≡⟨ sub-id-lemma η ⟩ 
        ⟦ idₛ ⟧-sub η 
        ≡⟨ sub-wk idₛ η ⟩ 
        ⟦ (λ x → var (there x)) ⟧-sub (η , V) 
        ∎)
        
    sub-V : ∀ { Γ Γ' X  } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (V : Γ' ⊢V: X)
        → ⟦ V ⟧-value (⟦ σ ⟧-sub η) ≡ ⟦ V [ σ ]ᵥ ⟧-value η
    sub-V {Γ' = Γ' ∷ X} σ η (var here) = refl
    sub-V {Γ' = Γ' ∷ X} σ η (var (there x)) = sub-V {Γ' = Γ'} (σ ∘ (there {Y = X})) η (var x)
    sub-V σ η (sub-value V p) = cong (coerceᵥ p) (sub-V σ η V)
    sub-V σ η ⟨⟩ = refl
    sub-V σ η ⟨ V , W ⟩ = cong₂ _,_ (sub-V σ η V) (sub-V σ η W)
    sub-V {Γ = Γ} {Γ' = Γ'} σ η (funU {X} M) = fun-ext (λ X' 
        → Eq.trans 
            (cong ⟦ M ⟧-user (cong₂ _,_ 
                (sub-wk σ η) 
                refl))
            (sub-U (extendₛ σ) (η , X') M))
    sub-V σ η (funK K) = fun-ext (λ X → 
        Eq.trans
            (cong ⟦ K ⟧-kernel (cong₂ _,_ 
                (sub-wk σ η) 
                refl))
            (sub-K (extendₛ σ) (η , X) K)) 
    sub-V {Γ} {Γ'} {Σ ⇒ Σ' , C'} σ η (runner {Σ} {Σ'} {C'} R) = fun-ext (λ op → fun-ext (λ x → fun-ext (λ par → 
        begin 
        ⟦ R op x ⟧-kernel (⟦ σ ⟧-sub η , par) 
        ≡⟨ cong ⟦ R op x ⟧-kernel (cong₂ _,_ (sub-wk σ η) refl) ⟩ 
        ⟦ R op x ⟧-kernel (⟦ (λ x₁ → σ x₁ [ there ]ᵥᵣ) ⟧-sub (η , par) , par)
        ≡⟨ refl ⟩
        ⟦ R op x ⟧-kernel (⟦ extendₛ {X = gnd (param op)} σ ⟧-sub (η , par)) 
        ≡⟨ sub-K (extendₛ σ) (η , par) (R op x) ⟩ 
        ⟦ R op x [ extendₛ σ ]ₖ ⟧-kernel (η , par)
        ≡⟨ cong (λ a → ⟦ a ⟧-kernel (η , par)) {y = sub-coop (R op x) σ} (sub-coop-lemma σ (R op x)) ⟩ 
        ⟦ sub-coop (R op x) σ ⟧-kernel (η , par)
        ≡⟨ refl ⟩
        refl
        )))
    --POTENTIAL TODO 11. 3.: use begin_ syntactic sugar to make the proofs prettier. 

    sub-U : ∀ { Γ Γ' Xᵤ } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (M : Γ' ⊢U: Xᵤ)
        → ⟦ M ⟧-user (⟦ σ ⟧-sub η) ≡ ⟦ M [ σ ]ᵤ ⟧-user η
    sub-U σ η (sub-user M p) = cong (coerceᵤ p) (sub-U σ η M)
    sub-U σ η (return V) = cong leaf (sub-V σ η V) 
    sub-U σ η (V · W) = cong₂ (λ a b → a b) (sub-V σ η V) (sub-V σ η W)
    sub-U {Γ} {Γ'} {X ! Σ} σ η (opᵤ {X'} op x par M) = cong₂ (node op x) (sub-V σ η par) (fun-ext (λ res → 
        (begin
        ⟦ M ⟧-user (⟦ σ ⟧-sub η , res)
        ≡⟨    (cong ⟦ M ⟧-user (cong₂ _,_ 
                (sub-wk σ η) 
                refl)) ⟩
        ⟦ M ⟧-user (⟦ extendₛ {Γ} {Γ'} {gnd (result op)} σ ⟧-sub (η , res))
        ≡⟨    (sub-U (extendₛ σ) (η , res) M)⟩
        ⟦ M [ extendₛ σ ]ᵤ ⟧-user (η , res)
        ∎)))
    sub-U σ η (`let M `in N) = cong₂ bind-tree 
        (fun-ext (λ X 
            → Eq.trans 
                (cong ⟦ N ⟧-user (cong₂ _,_ 
                                    (sub-wk σ η)
                                    refl))  
                (sub-U (extendₛ σ) (η , X) N) )) 
        (sub-U σ η M)
    sub-U σ η (match V `with M) = Eq.trans 
        (cong ⟦ M ⟧-user (cong₂ _,_ 
            (cong₂ _,_ 
                (begin 
                ⟦ σ ⟧-sub η 
                ≡⟨ sub-wk σ η ⟩ 
                ⟦ (λ x → σ x [ there ]ᵥᵣ) ⟧-sub (η , _) 
                ≡⟨ sub-wk (there ᵣ∘ₛ σ) (η , _) ⟩ 
                ⟦ (λ x → (there ᵣ∘ₛ σ) x [ there ]ᵥᵣ) ⟧-sub ((η , _ ), _) 
                ∎)
                (cong proj₁ (sub-V σ η V)))   
            (cong proj₂ (sub-V σ η V)))) 
        (sub-U (extendₛ (extendₛ σ)) ((η , proj₁ (⟦ V [ σ ]ᵥ ⟧-value η)) , proj₂ (⟦ V [ σ ]ᵥ ⟧-value η)) M)
    sub-U σ η (`using R at C `run M finally N) = cong₂ bind-tree 
        {x = (λ { (x , c') → ⟦ N ⟧-user ((⟦ σ ⟧-sub η , x) , c') })}
        {y = (λ { (x , c') → ⟦ N [ extendₛ (extendₛ σ) ]ᵤ ⟧-user ((η , x) , c')})}
        {u = (apply-runner (⟦ R ⟧-value (⟦ σ ⟧-sub η)) (⟦ M ⟧-user (⟦ σ ⟧-sub η)) (⟦ C ⟧-value (⟦ σ ⟧-sub η)))}
        {v = (apply-runner (⟦ R [ σ ]ᵥ ⟧-value η) (⟦ M [ σ ]ᵤ ⟧-user η) (⟦ C [ σ ]ᵥ ⟧-value η))}
            (fun-ext (λ (x , c') → 
                begin 
                ⟦ N ⟧-user ((⟦ σ ⟧-sub η , x) , c') 
                ≡⟨ cong ⟦ N ⟧-user (cong₂ _,_ 
                    (cong₂ _,_ 
                        (Eq.trans
                            (sub-wk σ η)
                            (sub-wk (wkₛ σ) (η , x)))
                        refl)
                    refl) ⟩ 
                ⟦ N ⟧-user ((⟦ (λ x₁ → (σ x₁ [ wkᵣ ]ᵥᵣ) [ wkᵣ ]ᵥᵣ) ⟧-sub ((η , x) , c') , x) , c') 
                ≡⟨ sub-U (extendₛ (extendₛ σ)) ((η , x) , c') N ⟩
                ⟦ N [ extendₛ (extendₛ σ) ]ᵤ ⟧-user ((η , x) , c') 
                ≡⟨ refl ⟩ 
                refl
                ))
            (cong₂ (λ a b → a b)
                {x = apply-runner (⟦ R ⟧-value (⟦ σ ⟧-sub η)) (⟦ M ⟧-user (⟦ σ ⟧-sub η))}
                {y = apply-runner (⟦ R [ σ ]ᵥ ⟧-value η) (⟦ M [ σ ]ᵤ ⟧-user η)}
                (cong₂ apply-runner 
                    {x = ⟦ R ⟧-value (⟦ σ ⟧-sub η)}
                    {y = ⟦ R [ σ ]ᵥ ⟧-value η}
                    {u = ⟦ M ⟧-user (⟦ σ ⟧-sub η)}
                    {v = ⟦ M [ σ ]ᵤ ⟧-user η}
                    (sub-V σ η R)
                    (sub-U σ η M))
                (sub-V σ η C))
    sub-U {Γ} {Γ'} {X' ! Σ} σ η (kernel K at C finally M) = cong₂ bind-tree
        {x = (λ { (X , C) → ⟦ M ⟧-user ((⟦ σ ⟧-sub η , X) , C) })}
        {y = (λ { (X , C) → ⟦ M [ extendₛ (extendₛ σ) ]ᵤ ⟧-user ((η , X) , C) })}
        {u = (⟦ K ⟧-kernel (⟦ σ ⟧-sub η) (⟦ C ⟧-value (⟦ σ ⟧-sub η)))}
        {v = (⟦ K [ σ ]ₖ ⟧-kernel η (⟦ C [ σ ]ᵥ ⟧-value η))}
            (fun-ext (λ (X , C) → Eq.trans 
                (cong ⟦ M ⟧-user (cong₂ _,_ 
                    (cong₂ _,_ 
                        (begin 
                        (⟦ σ ⟧-sub η 
                        ≡⟨ sub-wk σ η ⟩ 
                        ⟦ (λ x → σ x [ there ]ᵥᵣ) ⟧-sub (η , X) 
                        ≡⟨ sub-wk (there ᵣ∘ₛ σ) (η , X) ⟩ 
                        ⟦ (λ x → (there ᵣ∘ₛ σ) x [ there ]ᵥᵣ) ⟧-sub ((η , X) , C)
                        ∎
                        ))
                        refl)
                    refl)) 
                (sub-U (extendₛ (extendₛ σ)) (( η , X) , C) M  ))) 
            (cong₂ (λ a b → a b) 
                {x = ⟦ K ⟧-kernel (⟦ σ ⟧-sub η)}
                {y = ⟦ K [ σ ]ₖ ⟧-kernel η}
                {u = (⟦ C ⟧-value (⟦ σ ⟧-sub η))}
                {v = (⟦ C [ σ ]ᵥ ⟧-value η)}
                    (sub-K σ η K) 
                    (sub-V σ η C))

    sub-K : ∀ { Γ Γ' Xₖ  } (σ : Sub Γ Γ') (η : ⟦ Γ ⟧-ctx) (K : Γ' ⊢K: Xₖ)
        → (⟦ K ⟧-kernel (⟦ σ ⟧-sub η)) ≡ (⟦ K [ σ ]ₖ ⟧-kernel η) 
    sub-K σ η (sub-kernel K p) = cong (coerceₖ p) (sub-K σ η K) 
    sub-K σ η (return V) = fun-ext (λ C → cong leaf (cong₂ _,_ (sub-V σ η V) refl))
    sub-K σ η (V · W) = cong₂ (λ x y → x y) (sub-V σ η V) (sub-V σ η W)
    sub-K σ η (`let K `in L) = fun-ext (λ C → cong₂ bind-tree 
        (fun-ext (λ (X , C') → cong₂ (λ a b → a b) 
            {x = ⟦ L ⟧-kernel (⟦ σ ⟧-sub η , X)}
            {y = ⟦ L [ extendₛ σ ]ₖ ⟧-kernel (η , X)}
            {u = C'}
            {v = C'}
                (Eq.trans
                    (cong ⟦ L ⟧-kernel (cong₂ _,_
                        (sub-wk σ η)
                        refl))
                    (sub-K (extendₛ σ) (η , X) L))
                refl)) 
        (cong₂ (λ x y → x y) 
            (sub-K σ η K) 
            refl)) 
    sub-K σ η (match V `with K) = Eq.trans 
        (cong ⟦ K ⟧-kernel 
            (cong₂ _,_ 
                (cong₂ _,_
                    (begin 
                    ⟦ σ ⟧-sub η 
                    ≡⟨ sub-wk σ η ⟩ 
                    ⟦ (λ x → σ x [ there ]ᵥᵣ) ⟧-sub (η , proj₁ (⟦ V [ σ ]ᵥ ⟧-value η))
                    ≡⟨ sub-wk (there ᵣ∘ₛ σ) (η , proj₁ (⟦ V [ σ ]ᵥ ⟧-value η)) ⟩ 
                    ⟦ (λ x → (σ x [ (λ x₁ → there x₁) ]ᵥᵣ) [ (λ x₁ → there x₁) ]ᵥᵣ) ⟧-sub
                        ((η , proj₁ (⟦ V [ σ ]ᵥ ⟧-value η)) , proj₂ (⟦ V [ σ ]ᵥ ⟧-value η)) 
                    ∎) 
                    (cong proj₁ (sub-V σ η V))) (cong proj₂ (sub-V σ η V)) )) 
                (sub-K (extendₛ (extendₛ σ)) ((η , proj₁ (⟦ V [ σ ]ᵥ ⟧-value η)) , proj₂ (⟦ V [ σ ]ᵥ ⟧-value η)) K)
    sub-K σ η (opₖ op x par K) = fun-ext 
        (λ C → cong₂ (node op x) 
            (sub-V σ η par) 
            (fun-ext 
                (λ res → cong₂ (λ K C → K C) {x = ⟦ K ⟧-kernel (⟦ σ ⟧-sub η , res)} {y = ⟦ K [ extendₛ σ ]ₖ ⟧-kernel (η , res)} 
                    (Eq.trans 
                        (cong ⟦ K ⟧-kernel (cong₂ _,_ (sub-wk σ η) refl))  
                        (sub-K (extendₛ σ) (η , res) K)) 
                    refl)))  
    sub-K σ η (getenv K) = fun-ext 
        (λ C → cong₂ (λ a b → a b) {x = ⟦ K ⟧-kernel (⟦ σ ⟧-sub η , C)} {y = ⟦ K [ extendₛ σ ]ₖ ⟧-kernel (η , C)} {u = C} {v = C} 
            (Eq.trans 
                (cong ⟦ K ⟧-kernel (cong₂ _,_ (sub-wk σ η) refl))  
                (sub-K (extendₛ σ) (η , C) K)) 
            refl) 
    sub-K σ η (setenv C K) = fun-ext (λ C' → 
        cong₂ (λ a b → a b) 
            {x = ⟦ K ⟧-kernel (⟦ σ ⟧-sub η)}  
            {y = ⟦ K [ σ ]ₖ ⟧-kernel η} 
            {u = (⟦ C ⟧-value (⟦ σ ⟧-sub η))} 
            {v = (⟦ C [ σ ]ᵥ ⟧-value η)}
            (fun-ext (λ _ → cong₂ (λ a b → a b)
                {x = ⟦ K ⟧-kernel (⟦ σ ⟧-sub η)}
                {y = ⟦ K [ σ ]ₖ ⟧-kernel η}
                (sub-K σ η K)
                refl))
            (sub-V σ η C))
    sub-K σ η (user M `with K) = fun-ext (λ C → 
        cong₂ bind-tree 
            (fun-ext (λ X → 
                cong₂ (λ a b → a b) {x = ⟦ K ⟧-kernel (⟦ σ ⟧-sub η , X)} {y = ⟦ K [ extendₛ σ ]ₖ ⟧-kernel (η , X)} 
                    (Eq.trans 
                        (cong ⟦ K ⟧-kernel 
                            (cong₂ _,_ 
                                (sub-wk σ η)
                                refl))
                        (sub-K (extendₛ σ) (η , X) K))
                    refl)) 
            (sub-U σ η M)) 
                      
                                 
 