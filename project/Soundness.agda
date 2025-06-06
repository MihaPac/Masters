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
    valid-V {w = w} funU-eta η = fun-ext (λ x → 
        cong₂ (λ a b → a b) 
            {x = ⟦ w [ (λ x₁ → there x₁) ]ᵥᵣ ⟧-value (η , x)}
            {y = ⟦ w ⟧-value η}
            {u = x}
            {v = x}
            (Eq.sym (Eq.trans 
                (cong ⟦ w ⟧-value (Eq.trans
                    (ren-id-lemma η)
                    (ren-wk idᵣ η)))
                (ren-value w wkᵣ (η , x))))
            refl)
    valid-V {Γ} {X} {Xₖ} {w = w} funK-eta η = fun-ext (λ X → 
        cong₂ (λ a b → a b) 
            {x = ⟦ w [ (λ x₁ → there x₁) ]ᵥᵣ ⟧-value (η , X)}
            {y = ⟦ w ⟧-value η}
            (Eq.sym (Eq.trans
                (cong ⟦ w ⟧-value (Eq.trans
                    (ren-id-lemma η)
                    (ren-wk idᵣ η)))
                (ren-value w wkᵣ (η , X))))
            refl)
            {-Eq.sym (Eq.trans 
        (cong ⟦ w ⟧-value (Eq.trans 
            (ren-id-lemma η) 
            (ren-wk idᵣ η))) 
        (ren-value {! Xₖ  !} wkᵣ (η , {!   !})))
        TODO: Is it possible to do it without having to add a variable?-}

    valid-U refl η = Eq.refl
    valid-U (sym eq-m) η = Eq.sym (valid-U eq-m η) 
    valid-U (trans eq-m eq-n) η = Eq.trans (valid-U eq-m η) (valid-U eq-n η) 
    valid-U (return-cong eq-v) η = Eq.cong (λ x → leaf x) (valid-V eq-v η)
    valid-U {Γ} {Xᵤ} {m} {n} (·-cong eq-v eq-w) η = 
        cong₂ (λ v-value w-value → v-value w-value) 
            (valid-V eq-v η) 
            (valid-V eq-w η)
    valid-U (opᵤ-cong p eq-v eq-m) η = cong₂ (node _ p) (valid-V eq-v η) (fun-ext (λ res → valid-U eq-m (η , res))) 
    valid-U (let-in-cong eq-m eq-n) η = cong₂ bind-user (fun-ext (λ x → valid-U eq-n (η , x))) (valid-U eq-m η)
    valid-U (match-with-cong eq-v eq-m) η = cong₂ (λ m η' → m η') (fun-ext (λ η' → valid-U eq-m η')) (cong (λ x → ( η , proj₁ x) , proj₂ x) (valid-V eq-v η))
    valid-U (using-at-run-finally-cong eq-r eq-w eq-m eq-n) η = 
        cong₂ bind-tree (fun-ext (λ η' → valid-U eq-n ((η , proj₁ η') , proj₂ η') ))  
            (cong₂ (λ r,m w → apply-runner (proj₁ r,m) (proj₂ r,m) w)  
                (cong₂ (λ r m → r , m)  (valid-V eq-r η) (valid-U eq-m η)) 
                (valid-V eq-w η))
    valid-U (kernel-at-finally-cong eq-v eq-m eq-k) η = 
        cong₂ bind-tree 
            (fun-ext (λ x → valid-U eq-m ((η , proj₁ x) , proj₂ x))) 
            (cong₂ (λ k c → k c ) 
                (valid-K eq-k η) 
                (valid-V eq-v η))
    valid-U (funU-beta m v) η = Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (sub-id-lemma η) refl)) (sub-U (var ∷ₛ v) η m)
    valid-U (let-in-beta-return_ v m) η = Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (sub-id-lemma η) refl)) (sub-U (var ∷ₛ v) η m)
    --{X Y : VType} {Σ : Sig} for let-in-beta-op
    valid-U {Γ} {X ! Σ} (let-in-beta-op {X'} {Y} op x param m n) η = cong (node op x (⟦ param ⟧-value η)) 
        (fun-ext (λ res → cong₂ bind-tree
            {x = (λ X₁ → ⟦ n ⟧-user (η , X₁))}
            {y = (λ X₁ → ⟦ n [ extdᵣ (λ x₁ → there x₁) ]ᵤᵣ ⟧-user ((η , res) , X₁))}
            {u = (⟦ m ⟧-user (η , res))}
            {v = (⟦ m ⟧-user (η , res))}
            (fun-ext (λ x₁ → Eq.trans
                (cong ⟦ n ⟧-user (cong (_, x₁) 
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
                (ren-user n (extdᵣ (λ x₂ → there x₂)) ((η , res) , x₁))
                ))
            refl))
    valid-U (match-with-beta-prod v w m) η = Eq.trans 
        (cong ⟦ m ⟧-user (cong (_, ⟦ w ⟧-value η) (cong (_, ⟦ v ⟧-value η) (sub-id-lemma η)))) 
        (sub-U ((var ∷ₛ v) ∷ₛ w) η m)
    valid-U (using-run-finally-beta-return r w v m) η = Eq.trans (cong ⟦ m ⟧-user (cong₂ _,_ (cong₂ _,_ (sub-id-lemma η) refl) refl))
        (sub-U ((var ∷ₛ v) ∷ₛ w) η m)
    valid-U {Γ} {X ! Σ} (using-run-finally-beta-op {Σ'} {Σ} {C} {X'} {X} R w op param' p m n) η = 
        begin 
        ⟦ `using runner R at w `run opᵤ op p param' m finally n ⟧-user η
        ≡⟨ refl ⟩ 
        bind-tree (λ { (x , c') → ⟦ n ⟧-user ((η , x) , c') })
          (bind-tree
           (λ { (x , C')
                  → apply-runner (λ op₁ x₁ param₁ → ⟦ R op₁ x₁ ⟧-kernel (η , param₁))
                    (⟦ m ⟧-user (η , x)) C'
              })
           (⟦ R op p ⟧-kernel (η , ⟦ param' ⟧-value η) (⟦ w ⟧-value η)))
        ≡⟨ >>=-assoc-Tree {Σ = Σ} {l = lzero}
            (⟦ R op p ⟧-kernel (η , ⟦ param' ⟧-value η) (⟦ w ⟧-value η))
            (λ { (x , C')
              → apply-runner (λ op₁ x₁ param₁ → ⟦ R op₁ x₁ ⟧-kernel (η , param₁))
                (⟦ m ⟧-user (η , x)) C'})
            (λ { (x , c') → ⟦ n ⟧-user ((η , x) , c') }) ⟩ 
        bind-tree
          (λ (res , C₁) →
             bind-tree (λ { (x , c') → ⟦ n ⟧-user ((η , x) , c') })
             (apply-runner (λ op₁ x₁ param₁ → ⟦ R op₁ x₁ ⟧-kernel (η , param₁))
              (⟦ m ⟧-user (η , res))
              (C₁)))
          (⟦ R op p ⟧-kernel (η , ⟦ param' ⟧-value η) (⟦ w ⟧-value η))
        ≡⟨ cong₂ bind-tree
        {x = (λ (res , C₁) →
            bind-tree (λ { (x , c') → ⟦ n ⟧-user ((η , x) , c') })
            (apply-runner (λ op₁ x₁ param₁ → ⟦ R op₁ x₁ ⟧-kernel (η , param₁))
            (⟦ m ⟧-user (η , res))
            (C₁)))}
        {y = (λ { (X , C)
                → ⟦
                `using
                runner (λ op₁ p₁ → rename-coop (R op₁ p₁) (λ x → there (there x)))
                at var here `run m [ there ]ᵤᵣ finally
                (n [ extdᵣ (extdᵣ (λ x → there (there x))) ]ᵤᵣ)
                ⟧-user
                ((η , X) , C)
            })}
        {u = (⟦ R op p ⟧-kernel (η , ⟦ param' ⟧-value η) (⟦ w ⟧-value η))}
        {v = (⟦ R op p [ var ∷ₛ param' ]ₖ ⟧-kernel η (⟦ w ⟧-value η))}
        (fun-ext λ (res , C') → cong₂ bind-tree
            {x = (λ { (x , c') → ⟦ n ⟧-user ((η , x) , c') })}
            {y = (λ { (x , c')
                    → ⟦ n [ extdᵣ (extdᵣ (λ x₁ → there (there x₁))) ]ᵤᵣ ⟧-user
                    ((((η , res) , C') , x) , c') })}
            {u = (apply-runner (λ op₁ x₁ param₁ → ⟦ R op₁ x₁ ⟧-kernel (η , param₁))
                (⟦ m ⟧-user (η , res)) C')}
            {v = (apply-runner
                (λ op₁ x param₁ →
                    ⟦ rename-coop (R op₁ x) (λ x₁ → there (there x₁)) ⟧-kernel
                    (((η , res) , C') , param₁))
                (⟦ m [ there ]ᵤᵣ ⟧-user ((η , res) , C')) C')}
            (fun-ext (λ (X'' , C'') → 
                (begin
                ⟦ n ⟧-user ((η , X'') , C'')
                ≡⟨ cong ⟦ n ⟧-user (cong (λ a → (a , X'') , C'') 
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
                ⟦ n ⟧-user
                  (⟦ extdᵣ {X = gnd C} (extdᵣ {X = X'} (λ x₁ → there (there x₁))) ⟧-ren
                   ((((η , res) , C') , X'') , C''))
                ≡⟨ ren-user n (extdᵣ (extdᵣ (λ x₁ → there (there x₁)))) 
                    ((((η , res) , C') , X'') , C'') ⟩
                ⟦ n [ extdᵣ (extdᵣ (λ x₁ → there (there x₁))) ]ᵤᵣ ⟧-user
                  ((((η , res) , C') , X'') , C'')
                ∎
                )))
            (cong₂ (λ a b → apply-runner a b C')
                {x = (λ op₁ x₁ param₁ → ⟦ R op₁ x₁ ⟧-kernel (η , param₁))}
                {y = (λ op₁ x param₁ →
                    ⟦ rename-coop (R op₁ x) (λ x₁ → there (there x₁)) ⟧-kernel
                    (((η , res) , C') , param₁))}
                {u = (⟦ m ⟧-user (η , res))}
                {v = (⟦ m [ there ]ᵤᵣ ⟧-user ((η , res) , C'))}
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
                ⟦ m ⟧-user (η , res)
                ≡⟨ cong ⟦ m ⟧-user 
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
                ⟦ m ⟧-user (⟦ there {Y = gnd C} {Γ = Γ ∷ gnd (result op)} ⟧-ren 
                    ((η , res) , C'))
                ≡⟨ ren-user m there ((η , res) , C') ⟩ 
                ⟦ m [ there ]ᵤᵣ ⟧-user ((η , res) , C')
                ∎ 
                )))
        (cong (λ a → a (⟦ w ⟧-value η))
           {x = ⟦ R op p ⟧-kernel (η , ⟦ param' ⟧-value η)}
           {y = ⟦ R op p [ var ∷ₛ param' ]ₖ ⟧-kernel η} 
           (Eq.trans
                (cong ⟦ R op p ⟧-kernel 
                    (cong (_, ⟦ param' ⟧-value η) 
                        (sub-id-lemma η)))
                (sub-K (var ∷ₛ param') η (R op p))))
             ⟩ 
        bind-tree
          (λ { (X , C)
                 → ⟦
                   `using
                   runner (λ op₁ p₁ → rename-coop (R op₁ p₁) (λ x → there (there x)))
                   at var here `run m [ there ]ᵤᵣ finally
                   (n [ extdᵣ (extdᵣ (λ x → there (there x))) ]ᵤᵣ)
                   ⟧-user
                   ((η , X) , C)
             })
          (⟦ R op p [ var ∷ₛ param' ]ₖ ⟧-kernel η (⟦ w ⟧-value η))
        ≡⟨ refl ⟩
        ⟦
          kernel R op p [ var ∷ₛ param' ]ₖ at w finally
          (`using runner (rename-runner R (λ x → there (there x)))
           at var here `run m [ there ]ᵤᵣ finally
           (n [ extdᵣ (extdᵣ (λ x → there (there x))) ]ᵤᵣ))
          ⟧-user
          η
        ∎
    valid-U (kernel-at-finally-beta-return v c n) η = Eq.trans 
        (cong ⟦ n ⟧-user (cong (λ a → (a , ⟦ v ⟧-value η) , ⟦ c ⟧-value η) (sub-id-lemma η))) 
        (sub-U ((var ∷ₛ v) ∷ₛ c) η n) 
    valid-U (kernel-at-finally-beta-getenv c k m) η = cong₂ bind-tree
        {x = (λ { (X , C) → ⟦ m ⟧-user ((η , X) , C) })}
        {y = (λ { (X , C) → ⟦ m ⟧-user ((η , X) , C) })}
        {u = (⟦ k ⟧-kernel (η , ⟦ c ⟧-value η) (⟦ c ⟧-value η))}
        {v = (⟦ k [ var ∷ₛ c ]ₖ ⟧-kernel η (⟦ c ⟧-value η))}
        (fun-ext (λ (X , C) → refl))
        (cong (λ a → a (⟦ c ⟧-value η)) 
            {x = ⟦ k ⟧-kernel (η , ⟦ c ⟧-value η)} 
            {y = ⟦ k [ var ∷ₛ c ]ₖ ⟧-kernel η}
            (Eq.trans
                (cong ⟦ k ⟧-kernel (cong (_, ⟦ c ⟧-value η) (sub-id-lemma η)))
                (sub-K (var ∷ₛ c) η k)))
    valid-U (kernel-at-finally-setenv c c' k m) η = refl --Strange
    valid-U {Γ} {X ! Σ} (kernel-at-finally-beta-op {X₁} {Y₁} {Σ₁} {C₁} op p param c k m) η = 
        cong (node op p (⟦ param ⟧-value η)) (fun-ext (λ res → 
            cong₂ bind-tree
                {x = (λ { (X , C) → ⟦ m ⟧-user ((η , X) , C) })}
                {y = (λ { (X , C) → ⟦ m [ extdᵣ (extdᵣ (λ x → there x)) ]ᵤᵣ ⟧-user (((η , res) , X) , C) })}
                {u = (⟦ k ⟧-kernel (η , res) (⟦ c ⟧-value η))}
                {v = (⟦ k ⟧-kernel (η , res) (⟦ c [ (λ x → there x) ]ᵥᵣ ⟧-value (η , res)))}
                (fun-ext (λ (X , C) → 
                    begin 
                    ⟦ m ⟧-user ((η , X) , C)
                    ≡⟨ refl ⟩ 
                    ⟦ m ⟧-user ((η , X) , C)
                    ≡⟨ cong ⟦ m ⟧-user (cong (λ a → (a , X) , C) 
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
                    ⟦ m ⟧-user (⟦ extdᵣ {X = gnd C₁} (extdᵣ {X = X₁} there) ⟧-ren (((η , res) , X) , C))
                    ≡⟨ ren-user m (extdᵣ (extdᵣ there)) (((η , res) , X) , C) ⟩ 
                    ⟦ m [ extdᵣ (extdᵣ there) ]ᵤᵣ ⟧-user (((η , res) , X) , C)
                    ∎ 
                    ))
                (cong (⟦ k ⟧-kernel (η , res)) (Eq.trans
                    (cong ⟦ c ⟧-value (Eq.trans
                        (ren-id-lemma η)
                        (ren-wk idᵣ η)))
                    (ren-value c wkᵣ (η , res))))))
    valid-U {Γ} {X ! Σ} (let-in-eta-M n) η = begin
        bind-tree (λ X₁ → leaf X₁) (⟦ n ⟧-user η)
        ≡⟨ (Eq.cong-app {f = bind-tree (λ X₁ → leaf X₁) } {g = bind-tree leaf} refl (⟦ n ⟧-user η)) ⟩
        bind-tree leaf (⟦ n ⟧-user η)
        ≡⟨ η-right-Tree {Σ = Σ} {l = lzero} (⟦ n ⟧-user η) ⟩
        ⟦ n ⟧-user η
        ∎

    valid-K refl η = Eq.refl
    valid-K (sym eq-k) η = Eq.sym (valid-K eq-k η)
    valid-K (trans eq-k eq-l) η = Eq.trans (valid-K eq-k η) (valid-K eq-l η) 
    valid-K (return-cong eq-v) η = fun-ext (λ x → cong leaf (cong (λ y → (y , x)) (valid-V eq-v η))) 
    valid-K (·-cong eq-v eq-w) η = cong₂ (λ v-value w-value → v-value w-value) (valid-V eq-v η) (valid-V eq-w η) 
    valid-K (let-in-cong eq-k eq-l) η = 
        fun-ext (λ c → cong₂ bind-tree (fun-ext (λ x → cong (λ x₁ → x₁ (proj₂ x)) (valid-K eq-l (η , proj₁ x) )) )  (cong₂ (λ a b → a b) (valid-K eq-k η) refl) )
    valid-K (match-with-cong eq-v eq-k) η = cong₂ (λ k v → k v) (fun-ext (λ η' → valid-K eq-k η' )) (cong (λ v → (( η , proj₁ v ) , proj₂ v)) (valid-V eq-v η))
    valid-K (opₖ-cong {V} {W} {Σ} {C} {op} {p} {param} eq-v eq-k) η = 
        fun-ext (λ _ → cong₂ (node op p) 
            (valid-V eq-v η) 
            (fun-ext (λ res → cong₂ (λ k≡k' c → k≡k' c) 
                (valid-K eq-k (η , res))  
                refl ))) 
    valid-K (getenv-cong eq-k) η = fun-ext (λ c → cong₂ (λ k≡k' c' → k≡k' c') (valid-K eq-k (η , c)) refl)
    valid-K (setenv-cong eq-v eq-k) η = fun-ext (λ _ → cong₂ (λ k c → k c) (valid-K eq-k η) (valid-V eq-v η)) 
    valid-K (user-with-cong eq-m eq-k) η = fun-ext (λ _ → cong₂ bind-tree (cong₂ (λ f c x → f x c) (fun-ext (λ x → valid-K eq-k (η , x) ))  refl) (valid-U eq-m η))  
    valid-K (funK-beta k v) η = Eq.trans 
        (cong ⟦ k ⟧-kernel (cong (_, ⟦ v ⟧-value η) (sub-id-lemma η)))
        (sub-K (var ∷ₛ v) η k) 
    valid-K (let-in-beta-return v k) η = fun-ext (λ C → cong (λ a → a C) (valid-K (funK-beta k v) η)) 
    valid-K (let-in-beta-op {X} {Y} op p param k l) η = fun-ext (λ C → 
        cong (node op p (⟦ param ⟧-value η)) (fun-ext (λ res → 
            cong (λ a → bind-tree a (⟦ k ⟧-kernel (η , res) C)) 
                (fun-ext (λ (x , C') → cong (λ a → a C') 
                {x = ⟦ l ⟧-kernel (η , x) }
                {y = ⟦ l [ extdᵣ (λ x₁ → there x₁) ]ₖᵣ ⟧-kernel ((η , res) , x)}
                (begin 
                ⟦ l ⟧-kernel (η , x)
                ≡⟨ cong ⟦ l ⟧-kernel (cong (_, x) 
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
                ⟦ l ⟧-kernel (⟦ extdᵣ {X = X} there ⟧-ren ((η , res) , x)) 
                ≡⟨ ren-kernel l (extdᵣ (λ x₁ → there x₁)) ((η , res) , x) ⟩
                ⟦ l [ extdᵣ (λ x₁ → there x₁) ]ₖᵣ ⟧-kernel ((η , res) , x)
                ∎
                ))))))
    valid-K (let-in-beta-getenv {X} k l) η = fun-ext (λ C → 
        cong (λ a → bind-tree a (⟦ k ⟧-kernel (η , C) C)) 
            (fun-ext (λ (x , C') → 
                cong (λ a → a C')
                    {x = ⟦ l ⟧-kernel (η , x)}
                    {y = ⟦ l [ extdᵣ (λ x₁ → there x₁) ]ₖᵣ ⟧-kernel ((η , C) , x)}
                    (begin 
                    ⟦ l ⟧-kernel (η , x)
                    ≡⟨ cong ⟦ l ⟧-kernel (cong (_, x) 
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
                    ⟦ l ⟧-kernel
                    (⟦ extdᵣ {X = X} (λ x₁ → there x₁) ⟧-ren ((η , C) , x))
                    ≡⟨ ren-kernel l (extdᵣ (λ x₁ → (there x₁))) ((η , C) , x) ⟩ 
                    ⟦ l [ extdᵣ there ]ₖᵣ ⟧-kernel ((η , C) , x)
                    ∎))))
    valid-K (let-in-beta-setenv c k l) η = refl 
    valid-K (match-with-beta-prod v w k) η = Eq.trans
        (cong (λ a → ⟦ k ⟧-kernel ((a , ⟦ v ⟧-value η) , ⟦ w ⟧-value η)) (sub-id-lemma η))
        (sub-K ((var ∷ₛ v) ∷ₛ w) η k) 
    valid-K (user-with-beta-return v k) η = fun-ext (λ C → 
        cong (λ a → a C) 
            {x = ⟦ k ⟧-kernel (η , ⟦ v ⟧-value η)}
            {y = ⟦ k [ var ∷ₛ v ]ₖ ⟧-kernel η}
            (Eq.trans 
                (cong (λ a → ⟦ k ⟧-kernel (a , ⟦ v ⟧-value η)) 
                    (sub-id-lemma η))
                (sub-K (var ∷ₛ v) η k))) 
    valid-K (user-with-beta-op op p param m k) η = fun-ext (λ C → 
        cong (node op p (⟦ param ⟧-value η)) (fun-ext (λ res → 
            cong (λ a → bind-tree a (⟦ m ⟧-user (η , res))) 
                ((fun-ext (λ X → cong (λ a → a C)
                    {x = ⟦ k ⟧-kernel (η , X)}
                    {y = ⟦ k [ extdᵣ (λ x → there x) ]ₖᵣ ⟧-kernel ((η , res) , X)}
                    (Eq.trans
                        (cong ⟦ k ⟧-kernel (cong (_, X) 
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
                        (ren-kernel k (extdᵣ (λ x → there x)) ((η , res) , X)))))))))

    valid-K {Γ} {X ↯ Σ , C} (let-in-eta-K l) η = fun-ext (λ x → begin
        bind-tree (λ { (x , C') → leaf (x , C') }) (⟦ l ⟧-kernel η x)
        ≡⟨ (Eq.cong-app {f = bind-tree (λ { (x , C') → leaf (x , C') }) } 
            {g = bind-tree leaf} refl (⟦ l ⟧-kernel η x)) ⟩
        bind-tree leaf ((⟦ l ⟧-kernel η x))
        ≡⟨ η-right-Tree {Σ = Σ} {l = lzero} (⟦ l ⟧-kernel η x) ⟩
        ⟦ l ⟧-kernel η x
        ∎) 
    valid-K (GetSetenv k) η = 
        begin
        (λ C → ⟦ k [ there ]ₖᵣ ⟧-kernel (η , C) C)
        ≡⟨ fun-ext (λ C → cong (λ a → a C) 
             {x = ⟦ k [ there ]ₖᵣ ⟧-kernel (η , C)}
             {y = ⟦ k ⟧-kernel (⟦ there ⟧-ren (η , C))}
             (Eq.sym (ren-kernel k there (η , C)))) ⟩ 
        (λ C₁ → ⟦ k ⟧-kernel (⟦ there ⟧-ren (η , C₁)) C₁)
        ≡⟨ fun-ext (λ C → cong (λ a → ⟦ k ⟧-kernel a C) 
            (Eq.sym (ren-wk idᵣ η))) ⟩ 
        ⟦ k ⟧-kernel (⟦ (λ x → x) ⟧-ren η)
        ≡⟨ cong ⟦ k ⟧-kernel (Eq.sym (ren-id-lemma η)) ⟩ 
        ⟦ k ⟧-kernel η
        ∎
    valid-K (SetGetenv c k) η = fun-ext (λ _ → 
        cong (λ a → a (⟦ c ⟧-value η))
            {x = ⟦ k ⟧-kernel (η , ⟦ c ⟧-value η)}
            {y = ⟦ k [ var ∷ₛ c ]ₖ ⟧-kernel η}
            (Eq.trans 
                (cong ⟦ k ⟧-kernel (cong (_, ⟦ c ⟧-value η) (sub-id-lemma η)))
                (sub-K (var ∷ₛ c) η k))) 
    valid-K (SetSetenv c c' k) η = fun-ext (λ c'' → refl)
    valid-K (GetOpEnv op p param k) η = 
        fun-ext (λ C → 
        cong₂ (node op p) 
            (Eq.sym (Eq.trans 
                (cong ⟦ param ⟧-value (Eq.trans
                    (ren-id-lemma η)
                    (ren-wk idᵣ η)))
                (ren-value param there (η , C)))) 
            (fun-ext (λ res → cong (λ a → a C) 
                {x = ⟦ k [ (λ x → there (there x)) ]ₖᵣ ⟧-kernel ((η , C) , res)}
                {y = ⟦ k [ (λ x → there (there x)) ]ₖᵣ ⟧-kernel ((η , res) , C)}
                (begin 
                ⟦ k [ (λ x → there (there x)) ]ₖᵣ ⟧-kernel ((η , C) , res)
                ≡⟨ Eq.sym (ren-kernel k (λ x → there (there x)) ((η , C) , res)) ⟩
                ⟦ k ⟧-kernel
                  (⟦ (λ x → there (there x)) ⟧-ren ((η , C) , res))
                ≡⟨ cong ⟦ k ⟧-kernel (Eq.sym (Eq.trans
                    (ren-id-lemma η)
                    (Eq.trans
                        (ren-wk idᵣ η)
                        (ren-wk there (η , C))))) ⟩
                ⟦ k ⟧-kernel η
                ≡⟨ cong ⟦ k ⟧-kernel (Eq.trans
                    (ren-id-lemma η)
                    (Eq.trans
                        (ren-wk idᵣ η)
                        (ren-wk there (η , res)))) ⟩
                ⟦ k ⟧-kernel
                  (⟦ (λ x → there (there x)) ⟧-ren ((η , res) , C))
                ≡⟨ ren-kernel k (λ x → there (there x)) ((η , res) , C) ⟩
                ⟦ k [ (λ x → there (there x)) ]ₖᵣ ⟧-kernel ((η , res) , C)
                ∎
                )
                ))
            )  
    valid-K {Γ} {X ↯ Σ , C} (SetOpEnv {X'} {Σ'} op x param w k) η = fun-ext 
        (λ C' → cong (node op x (⟦ w ⟧-value η)) (fun-ext (λ res → 
            cong (⟦ k ⟧-kernel (η , res)) 
                (Eq.trans
                    (cong ⟦ param ⟧-value (Eq.trans
                        (ren-id-lemma η)
                        (ren-wk idᵣ η)))
                    (ren-value param there (η , res))))))       

 