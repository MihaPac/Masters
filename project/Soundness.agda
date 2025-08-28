open import Data.Unit
open import Data.Product
import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning

open import Function

open import Level        renaming (zero to lzero; suc to lsuc)
import Contexts
open import Parameters

module Soundness (G : GTypes) (O : Ops G) where

open GTypes G
open Ops O

open Contexts G O
open import Types G O
open import Terms G O
open import Trees G O 
open import Equations G O
open import Interpreter G O 
open import Renaming G O 
open import Substitution G O
open import Interpreter-Substitution G O
open import Interpreter-Renaming G O
open import Monads G O
 


mutual

    valid-V : ∀ {Γ : Ctx} {X : VType} {V W : Γ ⊢V: X} → (eq-V : Γ ⊢V V ≡ W) → ∀ η → ⟦ V ⟧-value η ≡ ⟦ W ⟧-value η
    valid-U : ∀ {Γ : Ctx} {Xᵤ : UType} {M N : Γ ⊢U: Xᵤ} → (eq-M : Γ ⊢U M ≡ N) → ∀ η → ⟦ M ⟧-user η ≡ ⟦ N ⟧-user η
    valid-K : ∀ {Γ : Ctx} {Xₖ : KType} {K L : Γ ⊢K: Xₖ} → (eq-K : Γ ⊢K K ≡ L) → ∀ η → ⟦ K ⟧-kernel η ≡ ⟦ L ⟧-kernel η

    valid-V refl η = Eq.refl
    valid-V (sym eq-V) η = Eq.sym (valid-V eq-V η)
    valid-V (trans eq-V eq-W) η = Eq.trans (valid-V eq-V η) (valid-V eq-W η)
    valid-V (prod-cong eq-V eq-W) η = Eq.cong₂ _,_ (valid-V eq-V η) (valid-V eq-W η)
    valid-V (funU-cong eq-M) η = fun-ext (λ x → valid-U eq-M (η , x))
    valid-V (funK-cong eq-K) η = fun-ext (λ x → valid-K eq-K (η , x)) 
    valid-V (runner-cong eq-K) η = fun-ext 
        (λ op → fun-ext (λ x → fun-ext (λ param → valid-K (eq-K op x) (η , param)))) 
    valid-V unit-eta η = Eq.refl
    valid-V {W = W} funU-eta η = fun-ext (λ X → 
        cong₂ (λ a b → a b) 
            {x = ⟦ W [ (λ x₁ → there x₁) ]ᵥᵣ ⟧-value (η , X)}
            {y = ⟦ W ⟧-value η}
            {u = X}
            {v = X}
            (Eq.sym (Eq.trans 
                (cong ⟦ W ⟧-value (Eq.trans
                    (ren-id-lemma η)
                    (ren-wk idᵣ η)))
                (ren-value W wkᵣ (η , X))))
            Eq.refl)
    valid-V {Γ} {X} {Xₖ} {W = W} funK-eta η = fun-ext (λ X → 
        cong₂ (λ a b → a b) 
            {x = ⟦ W [ (λ x₁ → there x₁) ]ᵥᵣ ⟧-value (η , X)}
            {y = ⟦ W ⟧-value η}
            (Eq.sym (Eq.trans
                (cong ⟦ W ⟧-value (Eq.trans
                    (ren-id-lemma η)
                    (ren-wk idᵣ η)))
                (ren-value W wkᵣ (η , X))))
            refl)

    valid-U refl η = Eq.refl
    valid-U (sym eq-M) η = Eq.sym (valid-U eq-M η) 
    valid-U (trans eq-M eq-N) η = Eq.trans (valid-U eq-M η) (valid-U eq-N η) 
    valid-U (return-cong eq-V) η = Eq.cong (λ x → leaf x) (valid-V eq-V η)
    valid-U {Γ} {Xᵤ} {M} {N} (·-cong eq-V eq-W) η = 
        cong₂ (λ V-value W-value → V-value W-value) 
            (valid-V eq-V η) 
            (valid-V eq-W η)
    valid-U (opᵤ-cong p eq-V eq-M) η = cong₂ (node _ p) 
        (valid-V eq-V η) 
        (fun-ext (λ res → valid-U eq-M (η , res))) 
    valid-U (let-in-cong eq-M eq-N) η = cong₂ bind-user 
        (fun-ext (λ x → valid-U eq-N (η , x))) 
        (valid-U eq-M η)
    valid-U (match-with-cong eq-V eq-M) η = cong₂ (λ M η' → M η') 
        (fun-ext (λ η' → valid-U eq-M η')) 
        (cong (λ x → ( η , proj₁ x) , proj₂ x) (valid-V eq-V η))
    valid-U (using-at-run-finally-cong eq-R eq-W eq-M eq-N) η = 
        cong₂ bind-tree 
            (fun-ext (λ η' → valid-U eq-N ((η , proj₁ η') , proj₂ η') ))  
            (cong₂ (λ R,M W → apply-runner (proj₁ R,M) (proj₂ R,M) W)  
                (cong₂ (λ R M → R , M)  (valid-V eq-R η) (valid-U eq-M η)) 
                (valid-V eq-W η))
    valid-U (kernel-at-finally-cong eq-V eq-M eq-K) η = 
        cong₂ bind-tree 
            (fun-ext (λ x → valid-U eq-M ((η , proj₁ x) , proj₂ x))) 
            (cong₂ (λ K C → K C ) 
                (valid-K eq-K η) 
                (valid-V eq-V η))
    valid-U (funU-beta M V) η = 
        begin 
        ⟦ funU M · V ⟧-user η
        ≡⟨ cong ⟦ M ⟧-user (cong₂ _,_ (sub-id-lemma η) refl) ⟩ 
        ⟦ M ⟧-user (⟦ var ⟧-sub η , ⟦ V ⟧-value η)
        ≡⟨ sub-U (var ∷ₛ V) η M ⟩ 
        ⟦ M [ var ∷ₛ V ]ᵤ ⟧-user η
        ∎
    valid-U (let-in-beta-return_ V M) η = 
        begin
        ⟦ M ⟧-user (η , ⟦ V ⟧-value η)
        ≡⟨ cong ⟦ M ⟧-user (cong₂ _,_ (sub-id-lemma η) refl) ⟩ 
        ⟦ M ⟧-user (⟦ var ⟧-sub η , ⟦ V ⟧-value η)
        ≡⟨ sub-U (var ∷ₛ V) η M ⟩ 
        ⟦ M [ var ∷ₛ V ]ᵤ ⟧-user η
        ∎
    valid-U {Γ} {X ! Σ} (let-in-beta-op {X'} {Y} op x param M N) η = cong 
        (node op x (⟦ param ⟧-value η)) 
        (fun-ext (λ res → cong₂ bind-tree
            {x = (λ X₁ → ⟦ N ⟧-user (η , X₁))}
            {y = (λ X₁ → ⟦ N [ extdᵣ (λ x₁ → there x₁) ]ᵤᵣ ⟧-user ((η , res) , X₁))}
            {u = (⟦ M ⟧-user (η , res))}
            {v = (⟦ M ⟧-user (η , res))}
            (fun-ext (λ x₁ → Eq.trans
                (cong ⟦ N ⟧-user (cong (_, x₁) 
                    (begin 
                    η
                    ≡⟨ ren-id-lemma η ⟩
                    ⟦ (λ x₂ → x₂) ⟧-ren η
                    ≡⟨ ren-wk idᵣ η ⟩
                    ⟦ there ⟧-ren (η , res)
                    ≡⟨ ren-wk (there) (η , res) ⟩
                    ⟦ (λ x₂ → there (there x₂)) ⟧-ren ((η , res) , x₁)
                    ∎
                    )))
                (ren-user N (extdᵣ (λ x₂ → there x₂)) ((η , res) , x₁))
                ))
            refl))
    valid-U (match-with-beta-prod V W M) η = 
        begin
        ⟦ match ⟨ V , W ⟩ `with M ⟧-user η
        ≡⟨ cong ⟦ M ⟧-user (cong (_, ⟦ W ⟧-value η) (cong (_, ⟦ V ⟧-value η) (sub-id-lemma η))) ⟩ 
        ⟦ M ⟧-user
          ((⟦ var ⟧-sub η , ⟦ V ⟧-value η) ,
           ⟦ W ⟧-value η)
        ≡⟨ sub-U ((var ∷ₛ V) ∷ₛ W) η M ⟩ 
        ⟦ M [ (var ∷ₛ V) ∷ₛ W ]ᵤ ⟧-user η
        ∎
    valid-U (using-run-finally-beta-return R W V M) η = 
        begin
        ⟦ `using R at W `run return V finally M ⟧-user η
        ≡⟨ cong ⟦ M ⟧-user (cong₂ _,_ (cong₂ _,_ (sub-id-lemma η) refl) refl) ⟩ 
        ⟦ M ⟧-user
          ((⟦ var ⟧-sub η , ⟦ V ⟧-value η) ,
           ⟦ W ⟧-value η)
        ≡⟨ sub-U ((var ∷ₛ V) ∷ₛ W) η M ⟩ 
        ⟦ M [ (var ∷ₛ V) ∷ₛ W ]ᵤ ⟧-user η
        ∎
    valid-U {Γ} {X ! Σ} (using-run-finally-beta-op {Σ'} {Σ} {C} {X'} {X} R W op param' x M N) η = 
        begin 
        ⟦ `using runner R at W `run opᵤ op x param' M finally N ⟧-user η
        ≡⟨ refl ⟩ 
        bind-tree (λ { (x , c') → ⟦ N ⟧-user ((η , x) , c') })
          (bind-tree
           (λ { (x , C')
                  → apply-runner (λ op₁ x₁ param₁ → ⟦ R op₁ x₁ ⟧-kernel (η , param₁))
                    (⟦ M ⟧-user (η , x)) C'
              })
           (⟦ R op x ⟧-kernel (η , ⟦ param' ⟧-value η) (⟦ W ⟧-value η)))
        ≡⟨ >>=-assoc-Tree {Σ = Σ} {l = lzero}
            (⟦ R op x ⟧-kernel (η , ⟦ param' ⟧-value η) (⟦ W ⟧-value η))
            (λ { (x , C')
              → apply-runner (λ op₁ x₁ param₁ → ⟦ R op₁ x₁ ⟧-kernel (η , param₁))
                (⟦ M ⟧-user (η , x)) C'})
            (λ { (x , c') → ⟦ N ⟧-user ((η , x) , c') }) ⟩ 
        bind-tree
          (λ (res , C₁) →
             bind-tree (λ { (x , c') → ⟦ N ⟧-user ((η , x) , c') })
             (apply-runner (λ op₁ x₁ param₁ → ⟦ R op₁ x₁ ⟧-kernel (η , param₁))
              (⟦ M ⟧-user (η , res))
              (C₁)))
          (⟦ R op x ⟧-kernel (η , ⟦ param' ⟧-value η) (⟦ W ⟧-value η))
        ≡⟨ cong₂ bind-tree
        {x = (λ (res , C₁) →
            bind-tree (λ { (x , c') → ⟦ N ⟧-user ((η , x) , c') })
            (apply-runner (λ op₁ x₁ param₁ → ⟦ R op₁ x₁ ⟧-kernel (η , param₁))
            (⟦ M ⟧-user (η , res))
            (C₁)))}
        {y = (λ { (X , C)
                → ⟦
                `using
                runner (λ op₁ p₁ → rename-coop (R op₁ p₁) (λ x → there (there x)))
                at var here `run M [ there ]ᵤᵣ finally
                (N [ extdᵣ (extdᵣ (λ x → there (there x))) ]ᵤᵣ)
                ⟧-user
                ((η , X) , C)
            })}
        {u = (⟦ R op x ⟧-kernel (η , ⟦ param' ⟧-value η) (⟦ W ⟧-value η))}
        {v = (⟦ R op x [ var ∷ₛ param' ]ₖ ⟧-kernel η (⟦ W ⟧-value η))}
        (fun-ext λ (res , C') → cong₂ bind-tree
            {x = (λ { (x , c') → ⟦ N ⟧-user ((η , x) , c') })}
            {y = (λ { (x , c')
                    → ⟦ N [ extdᵣ (extdᵣ (λ x₁ → there (there x₁))) ]ᵤᵣ ⟧-user
                    ((((η , res) , C') , x) , c') })}
            {u = (apply-runner (λ op₁ x₁ param₁ → ⟦ R op₁ x₁ ⟧-kernel (η , param₁))
                (⟦ M ⟧-user (η , res)) C')}
            {v = (apply-runner
                (λ op₁ x param₁ →
                    ⟦ rename-coop (R op₁ x) (λ x₁ → there (there x₁)) ⟧-kernel
                    (((η , res) , C') , param₁))
                (⟦ M [ there ]ᵤᵣ ⟧-user ((η , res) , C')) C')}
            (fun-ext (λ (X'' , C'') → 
                (begin
                ⟦ N ⟧-user ((η , X'') , C'')
                ≡⟨ cong ⟦ N ⟧-user (cong (λ a → (a , X'') , C'') 
                    (Eq.trans 
                        (ren-id-lemma η)
                        (begin 
                        ⟦ (λ x → x) ⟧-ren η
                        ≡⟨ ren-wk idᵣ η ⟩
                        ⟦ there ⟧-ren (η , res)
                        ≡⟨ ren-wk there (η , res) ⟩
                        ⟦ (λ x → there (there x)) ⟧-ren ((η , res) , C')
                        ≡⟨ ren-wk (there ∘ᵣ there) ((η , res) , C') ⟩ 
                        ⟦ (λ x → there (there (there x))) ⟧-ren (((η , res) , C') , X'')
                        ≡⟨ ren-wk (there ∘ᵣ (there ∘ᵣ there)) (((η , res) , C') , X'') ⟩ 
                        ⟦ (λ x → there (there (there (there x)))) ⟧-ren
                            ((((η , res) , C') , X'') , C'')
                        ∎
                        ))) ⟩
                ⟦ N ⟧-user
                  (⟦ extdᵣ {X = gnd C} (extdᵣ {X = X'} (λ x₁ → there (there x₁))) ⟧-ren
                   ((((η , res) , C') , X'') , C''))
                ≡⟨ ren-user N (extdᵣ (extdᵣ (λ x₁ → there (there x₁)))) 
                    ((((η , res) , C') , X'') , C'') ⟩
                ⟦ N [ extdᵣ (extdᵣ (λ x₁ → there (there x₁))) ]ᵤᵣ ⟧-user
                  ((((η , res) , C') , X'') , C'')
                ∎
                )))
            (cong₂ (λ a b → apply-runner a b C')
                {x = (λ op₁ x₁ param₁ → ⟦ R op₁ x₁ ⟧-kernel (η , param₁))}
                {y = (λ op₁ x param₁ →
                    ⟦ rename-coop (R op₁ x) (λ x₁ → there (there x₁)) ⟧-kernel
                    (((η , res) , C') , param₁))}
                {u = (⟦ M ⟧-user (η , res))}
                {v = (⟦ M [ there ]ᵤᵣ ⟧-user ((η , res) , C'))}
                (fun-ext (λ op' → fun-ext (λ x' → fun-ext (λ par' → 
                    Eq.trans --{A = ⟦ C ⟧g → Tree Σ (Data.Product.Σ ⟦ result op' ⟧g (λ x → ⟦ C ⟧g))}
                        (begin 
                        ⟦ R op' x' ⟧-kernel (η , par')
                        ≡⟨ cong ⟦ R op' x' ⟧-kernel 
                            (Eq.trans
                                (ren-id-lemma (η , par'))
                                (ren-wk idᵣ (η , par'))) ⟩ 
                        ⟦ R op' x' ⟧-kernel
                          (⟦ there {_} {gnd (result op)} {Γ ∷ gnd (param op')} ⟧-ren  ((η , par') , res))
                        ≡⟨ cong ⟦ R op' x' ⟧-kernel 
                            (cong (_, par') 
                                (ren-wk (there ∘ᵣ there) ((η , par') , res))) ⟩ 
                        ⟦ R op' x' ⟧-kernel
                          (⟦ (λ x → there {Y = gnd C} (there {Y = gnd (result op)} {Γ = Γ ∷ gnd (param op')} x)) ⟧-ren 
                            (((η , par') , res) , C'))
                        ≡⟨ ren-kernel (R op' x') (there ∘ᵣ there) (((η , par') , res) , C') ⟩ 
                        ⟦ R op' x' [ (λ x₁ → there (there x₁)) ]ₖᵣ ⟧-kernel 
                            ((((η , par') , res) , C'))
                        ≡⟨ (begin 
                            ⟦ R op' x' [ there ∘ᵣ there ]ₖᵣ ⟧-kernel
                                (((η , par') , res) , C')
                            ≡⟨ Eq.sym (ren-kernel (R op' x') (there ∘ᵣ there) 
                                (((η , par') , res) , C')) ⟩ 
                            ⟦ R op' x' ⟧-kernel
                              (⟦ (λ x → there (there {Y = gnd (result op)} {Γ = Γ ∷ gnd (param op')} x)) ⟧-ren 
                                (((η , par') , res) , C'))
                            ≡⟨ cong ⟦ R op' x' ⟧-kernel 
                                (cong (_, par') 
                                (Eq.sym (
                                    begin 
                                    η
                                    ≡⟨ ren-id-lemma η ⟩
                                    ⟦ idᵣ ⟧-ren η
                                    ≡⟨ ren-wk idᵣ η ⟩
                                    ⟦ there ⟧-ren (η , par')
                                    ≡⟨ ren-wk there (η , par') ⟩
                                    ⟦ there ∘ᵣ there ⟧-ren ((η , par') , res)
                                    ≡⟨ ren-wk (there ∘ᵣ there) ((η , par') , res) ⟩
                                    ⟦ (λ x → there (there (there x))) ⟧-ren (((η , par') , res) , C')
                                    ∎
                                    ))) ⟩ 
                            ⟦ R op' x' ⟧-kernel (η , par')
                            ≡⟨ cong ⟦ R op' x' ⟧-kernel 
                                (cong (_, par') 
                                    (begin
                                    η
                                    ≡⟨ ren-id-lemma η ⟩
                                    ⟦ idᵣ ⟧-ren η
                                    ≡⟨ ren-wk idᵣ η ⟩
                                    ⟦ there ⟧-ren (η , res)
                                    ≡⟨ ren-wk there (η , res) ⟩
                                    ⟦ there ∘ᵣ there ⟧-ren
                                      ((η , res) , C')
                                    ≡⟨ ren-wk (there ∘ᵣ there) ((η , res) , C') ⟩
                                    ⟦ (λ x → there (there (there x))) ⟧-ren (((η , res) , C') , par')
                                    ∎
                                )) ⟩ 
                            ⟦ R op' x' ⟧-kernel
                              (⟦ extdᵣ {X = gnd (param op')} (λ x → there {Y = gnd C} {Γ = Γ ∷ gnd (result op)} 
                                (there {Y = gnd (result op)} {Γ = Γ} x)) ⟧-ren 
                                    (((η , res) , C') , par'))
                            ≡⟨ ren-kernel (R op' x') (extdᵣ (there ∘ᵣ there)) (((η , res) , C') , par') ⟩ 
                            ⟦ R op' x' [ extdᵣ (there ∘ᵣ there) ]ₖᵣ ⟧-kernel
                              (((η , res) , C') , par')
                            ∎ 
                            ) ⟩
                        ⟦ R op' x' [ extdᵣ (λ x₁ → there (there x₁)) ]ₖᵣ ⟧-kernel
                            (((η , res) , C') , par')
                        ∎
                        )
                        (cong (λ a → ⟦ a ⟧-kernel (((η , res) , C') , par'))
                            {y = rename-coop (R op' x') (λ x₁ → there (there x₁))}
                            (ren-coop-lemma (λ x₁ → there (there x₁)) (R op' x')))))))
                (begin 
                ⟦ M ⟧-user (η , res)
                ≡⟨ cong ⟦ M ⟧-user 
                    (cong (_, res) 
                        (Eq.trans
                            (ren-id-lemma η)
                            (begin 
                            ⟦ (λ x → x) ⟧-ren η
                            ≡⟨ ren-wk idᵣ η ⟩
                            ⟦ there ⟧-ren (η , res)
                            ≡⟨ ren-wk there (η , res) ⟩
                            ⟦ (λ x → there (there x)) ⟧-ren ((η , res) , C')
                            ∎
                            ))) ⟩ 
                ⟦ M ⟧-user (⟦ there {Y = gnd C} {Γ = Γ ∷ gnd (result op)} ⟧-ren 
                    ((η , res) , C'))
                ≡⟨ ren-user M there ((η , res) , C') ⟩ 
                ⟦ M [ there ]ᵤᵣ ⟧-user ((η , res) , C')
                ∎ 
                )))
        (cong (λ a → a (⟦ W ⟧-value η))
           {x = ⟦ R op x ⟧-kernel (η , ⟦ param' ⟧-value η)}
           {y = ⟦ R op x [ var ∷ₛ param' ]ₖ ⟧-kernel η} 
           (Eq.trans
                (cong ⟦ R op x ⟧-kernel 
                    (cong (_, ⟦ param' ⟧-value η) 
                        (sub-id-lemma η)))
                (sub-K (var ∷ₛ param') η (R op x))))
             ⟩ 
        bind-tree
          (λ { (X , C)
                 → ⟦
                   `using
                   runner (λ op₁ p₁ → rename-coop (R op₁ p₁) (λ x → there (there x)))
                   at var here `run M [ there ]ᵤᵣ finally
                   (N [ extdᵣ (extdᵣ (λ x → there (there x))) ]ᵤᵣ)
                   ⟧-user
                   ((η , X) , C)
             })
          (⟦ R op x [ var ∷ₛ param' ]ₖ ⟧-kernel η (⟦ W ⟧-value η))
        ≡⟨ refl ⟩
        ⟦
          kernel R op x [ var ∷ₛ param' ]ₖ at W finally
          (`using runner (rename-runner R (λ x → there (there x)))
           at var here `run M [ there ]ᵤᵣ finally
           (N [ extdᵣ (extdᵣ (λ x → there (there x))) ]ᵤᵣ))
          ⟧-user
          η
        ∎
    valid-U (kernel-at-finally-beta-return V C N) η = Eq.trans 
        (cong ⟦ N ⟧-user (cong (λ a → (a , ⟦ V ⟧-value η) , ⟦ C ⟧-value η) (sub-id-lemma η))) 
        (sub-U ((var ∷ₛ V) ∷ₛ C) η N) 
    valid-U (kernel-at-finally-beta-getenv C K M) η = cong₂ bind-tree
        {x = (λ { (X , C) → ⟦ M ⟧-user ((η , X) , C) })}
        {y = (λ { (X , C) → ⟦ M ⟧-user ((η , X) , C) })}
        {u = (⟦ K ⟧-kernel (η , ⟦ C ⟧-value η) (⟦ C ⟧-value η))}
        {v = (⟦ K [ var ∷ₛ C ]ₖ ⟧-kernel η (⟦ C ⟧-value η))}
        (fun-ext (λ (X , C) → refl))
        (cong (λ a → a (⟦ C ⟧-value η)) 
            {x = ⟦ K ⟧-kernel (η , ⟦ C ⟧-value η)} 
            {y = ⟦ K [ var ∷ₛ C ]ₖ ⟧-kernel η}
            (Eq.trans
                (cong ⟦ K ⟧-kernel (cong (_, ⟦ C ⟧-value η) (sub-id-lemma η)))
                (sub-K (var ∷ₛ C) η K)))
    valid-U (kernel-at-finally-setenv C c' K M) η = refl --Strange
    valid-U {Γ} {X ! Σ} (kernel-at-finally-beta-op {X₁} {Y₁} {Σ₁} {C₁} op x param C K M) η = 
        cong (node op x (⟦ param ⟧-value η)) (fun-ext (λ res → 
            cong₂ bind-tree
                {x = (λ { (X , C) → ⟦ M ⟧-user ((η , X) , C) })}
                {y = (λ { (X , C) → ⟦ M [ extdᵣ (extdᵣ (λ x → there x)) ]ᵤᵣ ⟧-user (((η , res) , X) , C) })}
                {u = (⟦ K ⟧-kernel (η , res) (⟦ C ⟧-value η))}
                {v = (⟦ K ⟧-kernel (η , res) (⟦ C [ (λ x → there x) ]ᵥᵣ ⟧-value (η , res)))}
                (fun-ext (λ (X , C) → 
                    begin 
                    ⟦ M ⟧-user ((η , X) , C)
                    ≡⟨ refl ⟩ 
                    ⟦ M ⟧-user ((η , X) , C)
                    ≡⟨ cong ⟦ M ⟧-user (cong (λ a → (a , X) , C) 
                        (begin 
                        η
                        ≡⟨ ren-id-lemma η ⟩
                        ⟦ (λ x → x) ⟧-ren η
                        ≡⟨ ren-wk idᵣ η ⟩
                        ⟦ there ⟧-ren (η , res)
                        ≡⟨ ren-wk there (η , res) ⟩
                        ⟦ (λ x → there (there x)) ⟧-ren ((η , res) , X)
                        ≡⟨ ren-wk (λ x → there (there x)) ((η , res) , X) ⟩
                        ⟦ (λ x → there (there (there x))) ⟧-ren (((η , res) , X) , C)
                        ∎)) ⟩
                    ⟦ M ⟧-user (⟦ extdᵣ {X = gnd C₁} (extdᵣ {X = X₁} there) ⟧-ren (((η , res) , X) , C))
                    ≡⟨ ren-user M (extdᵣ (extdᵣ there)) (((η , res) , X) , C) ⟩ 
                    ⟦ M [ extdᵣ (extdᵣ there) ]ᵤᵣ ⟧-user (((η , res) , X) , C)
                    ∎ 
                    ))
                (cong (⟦ K ⟧-kernel (η , res)) (Eq.trans
                    (cong ⟦ C ⟧-value (Eq.trans
                        (ren-id-lemma η)
                        (ren-wk idᵣ η)))
                    (ren-value C wkᵣ (η , res))))))
    valid-U {Γ} {X ! Σ} (let-in-eta-M N) η = begin
        bind-tree (λ X₁ → leaf X₁) (⟦ N ⟧-user η)
        ≡⟨ (Eq.cong-app {f = bind-tree (λ X₁ → leaf X₁) } {g = bind-tree leaf} refl (⟦ N ⟧-user η)) ⟩
        bind-tree leaf (⟦ N ⟧-user η)
        ≡⟨ η-right-Tree {Σ = Σ} {l = lzero} (⟦ N ⟧-user η) ⟩
        ⟦ N ⟧-user η
        ∎

    valid-K refl η = Eq.refl
    valid-K (sym eq-K) η = Eq.sym (valid-K eq-K η)
    valid-K (trans eq-K eq-L) η = Eq.trans (valid-K eq-K η) (valid-K eq-L η) 
    valid-K (return-cong eq-V) η = fun-ext (λ x → cong leaf (cong (λ y → (y , x)) (valid-V eq-V η))) 
    valid-K (·-cong eq-V eq-W) η = cong₂ (λ V-value W-value → V-value W-value) (valid-V eq-V η) (valid-V eq-W η) 
    valid-K (let-in-cong eq-K eq-L) η = 
        fun-ext (λ C → cong₂ bind-tree (fun-ext (λ x → cong (λ x₁ → x₁ (proj₂ x)) (valid-K eq-L (η , proj₁ x) )) )  (cong₂ (λ a b → a b) (valid-K eq-K η) refl) )
    valid-K (match-with-cong eq-V eq-K) η = cong₂ (λ K V → K V) (fun-ext (λ η' → valid-K eq-K η' )) (cong (λ V → (( η , proj₁ V ) , proj₂ V)) (valid-V eq-V η))
    valid-K (opₖ-cong {V} {W} {Σ} {C} {op} {x} {param} eq-V eq-K) η = 
        fun-ext (λ _ → cong₂ (node op x) 
            (valid-V eq-V η) 
            (fun-ext (λ res → cong₂ (λ k≡k' C → k≡k' C) 
                (valid-K eq-K (η , res))  
                refl ))) 
    valid-K (getenv-cong eq-K) η = fun-ext (λ C → cong₂ (λ k≡k' c' → k≡k' c') (valid-K eq-K (η , C)) refl)
    valid-K (setenv-cong eq-V eq-K) η = fun-ext (λ _ → cong₂ (λ K C → K C) (valid-K eq-K η) (valid-V eq-V η)) 
    valid-K (user-with-cong eq-M eq-K) η = fun-ext (λ _ → cong₂ bind-tree (cong₂ (λ f C x → f x C) (fun-ext (λ x → valid-K eq-K (η , x) ))  refl) (valid-U eq-M η))  
    valid-K (funK-beta K V) η = Eq.trans 
        (cong ⟦ K ⟧-kernel (cong (_, ⟦ V ⟧-value η) (sub-id-lemma η)))
        (sub-K (var ∷ₛ V) η K) 
    valid-K (let-in-beta-return V K) η = fun-ext (λ C → cong (λ a → a C) (valid-K (funK-beta K V) η)) 
    valid-K (let-in-beta-op {X} {Y} op x param K L) η = fun-ext (λ C → 
        cong (node op x (⟦ param ⟧-value η)) (fun-ext (λ res → 
            cong (λ a → bind-tree a (⟦ K ⟧-kernel (η , res) C)) 
                (fun-ext (λ (x , C') → cong (λ a → a C') 
                {x = ⟦ L ⟧-kernel (η , x) }
                {y = ⟦ L [ extdᵣ (λ x₁ → there x₁) ]ₖᵣ ⟧-kernel ((η , res) , x)}
                (begin 
                ⟦ L ⟧-kernel (η , x)
                ≡⟨ cong ⟦ L ⟧-kernel (cong (_, x) 
                    (begin 
                    η
                    ≡⟨ ren-id-lemma η ⟩
                    ⟦ idᵣ ⟧-ren η
                    ≡⟨ ren-wk idᵣ η ⟩
                    ⟦ there ⟧-ren (η , res)
                    ≡⟨ ren-wk there (η , res) ⟩ 
                    ⟦ (λ x₁ → there (there x₁)) ⟧-ren ((η , res) , x)
                    ∎
                    )) ⟩ 
                ⟦ L ⟧-kernel (⟦ extdᵣ {X = X} there ⟧-ren ((η , res) , x)) 
                ≡⟨ ren-kernel L (extdᵣ (λ x₁ → there x₁)) ((η , res) , x) ⟩
                ⟦ L [ extdᵣ (λ x₁ → there x₁) ]ₖᵣ ⟧-kernel ((η , res) , x)
                ∎
                ))))))
    valid-K (let-in-beta-getenv {X} K L) η = fun-ext (λ C → 
        cong (λ a → bind-tree a (⟦ K ⟧-kernel (η , C) C)) 
            (fun-ext (λ (x , C') → 
                cong (λ a → a C')
                    {x = ⟦ L ⟧-kernel (η , x)}
                    {y = ⟦ L [ extdᵣ (λ x₁ → there x₁) ]ₖᵣ ⟧-kernel ((η , C) , x)}
                    (begin 
                    ⟦ L ⟧-kernel (η , x)
                    ≡⟨ cong ⟦ L ⟧-kernel (cong (_, x) 
                        (begin
                        η 
                        ≡⟨ ren-id-lemma η ⟩
                        ⟦ idᵣ ⟧-ren η
                        ≡⟨ ren-wk idᵣ η ⟩
                        ⟦ there ⟧-ren (η , C)
                        ≡⟨ ren-wk there (η , C) ⟩ 
                        ⟦ (λ x₁ → (there (there x₁))) ⟧-ren ((η , C) , x)
                        ∎
                        )) ⟩
                    ⟦ L ⟧-kernel
                    (⟦ extdᵣ {X = X} (λ x₁ → there x₁) ⟧-ren ((η , C) , x))
                    ≡⟨ ren-kernel L (extdᵣ (λ x₁ → (there x₁))) ((η , C) , x) ⟩ 
                    ⟦ L [ extdᵣ there ]ₖᵣ ⟧-kernel ((η , C) , x)
                    ∎))))
    valid-K (let-in-beta-setenv C K L) η = refl 
    valid-K (match-with-beta-prod V W K) η = Eq.trans
        (cong (λ a → ⟦ K ⟧-kernel ((a , ⟦ V ⟧-value η) , ⟦ W ⟧-value η)) (sub-id-lemma η))
        (sub-K ((var ∷ₛ V) ∷ₛ W) η K) 
    valid-K (user-with-beta-return V K) η = fun-ext (λ C → 
        cong (λ a → a C) 
            {x = ⟦ K ⟧-kernel (η , ⟦ V ⟧-value η)}
            {y = ⟦ K [ var ∷ₛ V ]ₖ ⟧-kernel η}
            (Eq.trans 
                (cong (λ a → ⟦ K ⟧-kernel (a , ⟦ V ⟧-value η)) 
                    (sub-id-lemma η))
                (sub-K (var ∷ₛ V) η K))) 
    valid-K (user-with-beta-op op x param M K) η = fun-ext (λ C → 
        cong (node op x (⟦ param ⟧-value η)) (fun-ext (λ res → 
            cong (λ a → bind-tree a (⟦ M ⟧-user (η , res))) 
                ((fun-ext (λ X → cong (λ a → a C)
                    {x = ⟦ K ⟧-kernel (η , X)}
                    {y = ⟦ K [ extdᵣ (λ x → there x) ]ₖᵣ ⟧-kernel ((η , res) , X)}
                    (Eq.trans
                        (cong ⟦ K ⟧-kernel (cong (_, X) 
                            (begin 
                            η
                            ≡⟨ ren-id-lemma η ⟩ 
                            ⟦ idᵣ ⟧-ren η
                            ≡⟨ ren-wk idᵣ η ⟩
                            ⟦ there ⟧-ren (η , res)
                            ≡⟨ ren-wk there (η , res) ⟩
                            ⟦ (λ x → there (there x)) ⟧-ren ((η , res) , X)
                            ∎ 
                            )))
                        (ren-kernel K (extdᵣ (λ x → there x)) ((η , res) , X)))))))))

    valid-K {Γ} {X ↯ Σ , C} (let-in-eta-K L) η = fun-ext (λ x → begin
        bind-tree (λ { (x , C') → leaf (x , C') }) (⟦ L ⟧-kernel η x)
        ≡⟨ (Eq.cong-app {f = bind-tree (λ { (x , C') → leaf (x , C') }) } 
            {g = bind-tree leaf} refl (⟦ L ⟧-kernel η x)) ⟩
        bind-tree leaf ((⟦ L ⟧-kernel η x))
        ≡⟨ η-right-Tree {Σ = Σ} {l = lzero} (⟦ L ⟧-kernel η x) ⟩
        ⟦ L ⟧-kernel η x
        ∎) 
    valid-K (GetSetenv K) η = 
        begin
        (λ C → ⟦ K [ there ]ₖᵣ ⟧-kernel (η , C) C)
        ≡⟨ fun-ext (λ C → cong (λ a → a C) 
             {x = ⟦ K [ there ]ₖᵣ ⟧-kernel (η , C)}
             {y = ⟦ K ⟧-kernel (⟦ there ⟧-ren (η , C))}
             (Eq.sym (ren-kernel K there (η , C)))) ⟩ 
        (λ C₁ → ⟦ K ⟧-kernel (⟦ there ⟧-ren (η , C₁)) C₁)
        ≡⟨ fun-ext (λ C → cong (λ a → ⟦ K ⟧-kernel a C) 
            (Eq.sym (ren-wk idᵣ η))) ⟩ 
        ⟦ K ⟧-kernel (⟦ (λ x → x) ⟧-ren η)
        ≡⟨ cong ⟦ K ⟧-kernel (Eq.sym (ren-id-lemma η)) ⟩ 
        ⟦ K ⟧-kernel η
        ∎
    valid-K (SetGetenv C K) η = fun-ext (λ _ → 
        cong (λ a → a (⟦ C ⟧-value η))
            {x = ⟦ K ⟧-kernel (η , ⟦ C ⟧-value η)}
            {y = ⟦ K [ var ∷ₛ C ]ₖ ⟧-kernel η}
            (Eq.trans 
                (cong ⟦ K ⟧-kernel (cong (_, ⟦ C ⟧-value η) (sub-id-lemma η)))
                (sub-K (var ∷ₛ C) η K))) 
    valid-K (SetSetenv C c' K) η = fun-ext (λ c'' → refl)
    valid-K (GetOpEnv op x param K) η = 
        fun-ext (λ C → 
        cong₂ (node op x) 
            (Eq.sym (Eq.trans 
                (cong ⟦ param ⟧-value (Eq.trans
                    (ren-id-lemma η)
                    (ren-wk idᵣ η)))
                (ren-value param there (η , C)))) 
            (fun-ext (λ res → cong (λ a → a C) 
                {x = ⟦ K [ (λ x → there (there x)) ]ₖᵣ ⟧-kernel ((η , C) , res)}
                {y = ⟦ K [ (λ x → there (there x)) ]ₖᵣ ⟧-kernel ((η , res) , C)}
                (begin 
                ⟦ K [ (λ x → there (there x)) ]ₖᵣ ⟧-kernel ((η , C) , res)
                ≡⟨ Eq.sym (ren-kernel K (λ x → there (there x)) ((η , C) , res)) ⟩
                ⟦ K ⟧-kernel
                  (⟦ (λ x → there (there x)) ⟧-ren ((η , C) , res))
                ≡⟨ cong ⟦ K ⟧-kernel (Eq.sym (Eq.trans
                    (ren-id-lemma η)
                    (Eq.trans
                        (ren-wk idᵣ η)
                        (ren-wk there (η , C))))) ⟩
                ⟦ K ⟧-kernel η
                ≡⟨ cong ⟦ K ⟧-kernel (Eq.trans
                    (ren-id-lemma η)
                    (Eq.trans
                        (ren-wk idᵣ η)
                        (ren-wk there (η , res)))) ⟩
                ⟦ K ⟧-kernel
                  (⟦ (λ x → there (there x)) ⟧-ren ((η , res) , C))
                ≡⟨ ren-kernel K (λ x → there (there x)) ((η , res) , C) ⟩
                ⟦ K [ (λ x → there (there x)) ]ₖᵣ ⟧-kernel ((η , res) , C)
                ∎
                )
                ))
            )  
    valid-K {Γ} {X ↯ Σ , C} (SetOpEnv {X'} {Σ'} op x param W K) η = fun-ext 
        (λ C' → cong (node op x (⟦ W ⟧-value η)) (fun-ext (λ res → 
            cong (⟦ K ⟧-kernel (η , res)) 
                (Eq.trans
                    (cong ⟦ param ⟧-value (Eq.trans
                        (ren-id-lemma η)
                        (ren-wk idᵣ η)))
                    (ren-value param there (η , res))))))       

 