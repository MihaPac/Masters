open import Parameters

module Equations (G : GTypes) (O : Ops G) where

open import Types G O
open import Terms G O
open import Contexts G O
open import Renaming G O
open import Substitution G O


open GTypes G
open Ops O

interleaved mutual

  data _⊢V_≡_ (Γ : Ctx) : {X : VType} → Γ ⊢V: X → Γ ⊢V: X → Set
  data _⊢U_≡_ (Γ : Ctx) : {Xᵤ : UType} → Γ ⊢U: Xᵤ → Γ ⊢U: Xᵤ → Set
  data _⊢K_≡_ (Γ : Ctx) : {Xₖ : KType} → Γ ⊢K: Xₖ → Γ ⊢K: Xₖ → Set

  data _⊢V_≡_ where

    -- equivalence rules

    refl : {X : VType} {V : Γ ⊢V: X}
          ---------------------------
          → Γ ⊢V V ≡ V

    sym : {X : VType} {V V' : Γ ⊢V: X}
      → Γ ⊢V V ≡ V'
      --------------------
      → Γ ⊢V V' ≡ V

    trans : {X : VType} {V V' V'' : Γ ⊢V: X}
      → Γ ⊢V V ≡ V'
      → Γ ⊢V V' ≡ V''
      --------------------------
      → Γ ⊢V V ≡ V''

    -- congruence rules

    prod-cong :
      {X Y : VType}
      {V V' : Γ ⊢V: X}
      {W W' : Γ ⊢V: Y}
      → Γ ⊢V V ≡ V'
      → Γ ⊢V W ≡ W'
      -----------------------------
      → Γ ⊢V ⟨ V , W ⟩ ≡ ⟨ V' , W' ⟩

    funU-cong :
        {X : VType} {Xᵤ : UType}
        {M N : Γ ∷ X ⊢U: Xᵤ}
      → (Γ ∷ X) ⊢U M ≡ N
      -------------------------
      → Γ ⊢V (funU M) ≡ (funU N)

    funK-cong :
      {X : VType} {Xₖ : KType}
      {K L : (Γ ∷ X) ⊢K: Xₖ}
      → (Γ ∷ X) ⊢K K ≡ L
      -----------------
      → Γ ⊢V (funK K) ≡ (funK L)

    runner-cong :
      {X : VType} {Σ Σ' : Sig} {C : KState}
      {R R' : ((op : Op) → (op ∈ₒ Σ) → co-op Γ Σ' C op)}
      → ((op : Op) → (x : op ∈ₒ Σ) → (Γ ∷ gnd (param op)) ⊢K R op x ≡ R' op x)
      ------------------------------------------------------------------------
      → Γ ⊢V runner R ≡ runner R'

    -- rules from the paper


    unit-eta : {V : Γ ⊢V: gnd unit}
      ----------------------
      → Γ ⊢V V ≡ ⟨⟩

    funU-eta : {X : VType} {Xᵤ : UType}
      {V : Γ ⊢V: X ⟶ᵤ Xᵤ}
      ------------
      → Γ ⊢V funU ((V [ wkᵣ ]ᵥᵣ) · var here) ≡ V

    funK-eta : {X : VType} {Xₖ : KType}
      {V : Γ ⊢V: X ⟶ₖ Xₖ}
      ---------------
      → Γ ⊢V funK ((V [ wkᵣ ]ᵥᵣ) · (var here)) ≡ V




  data _⊢U_≡_ where

    -- equivalence rules
    refl : {Xᵤ : UType} {M : Γ ⊢U: Xᵤ}
          ---------------------------
          → Γ ⊢U M ≡ M

    sym : {Xᵤ : UType} {M M' : Γ ⊢U: Xᵤ}
      → Γ ⊢U M ≡ M'
      --------------------
      → Γ ⊢U M' ≡ M

    trans : {Xᵤ : UType} { M M' M'' : Γ ⊢U: Xᵤ}
      → Γ ⊢U M ≡ M'
      → Γ ⊢U M' ≡ M''
      --------------------------
      → Γ ⊢U M ≡ M''

    -- congruence rules

    return-cong :
      {X : VType} {V W : Γ ⊢V: X}
      {Σ : Sig}
      → Γ ⊢V V ≡ W
      ------------------
      → Γ ⊢U return {Σ = Σ} V ≡ return W

    ·-cong :
      {X : VType} {Xᵤ : UType}
      {V V' : Γ ⊢V: X ⟶ᵤ Xᵤ}
      {W W' : Γ ⊢V: X}
      → Γ ⊢V V ≡ V'
      → Γ ⊢V W ≡ W'
      ----------------------
      → Γ ⊢U V · W ≡ (V' · W')

    opᵤ-cong :
      {X : VType} {Σ : Sig}
      {op : Op}
      {V V' : Γ ⊢V: gnd (param op)}
      {M M' : Γ ∷ gnd (result op) ⊢U: X ! Σ}
      → (x : op ∈ₒ Σ)
      → Γ ⊢V V ≡ V'
      → (Γ ∷ gnd (result op)) ⊢U M ≡ M'
      --------------------
      → Γ ⊢U opᵤ op x V M ≡ opᵤ op x V' M'

    let-in-cong :
      {X Y : VType} {Σ : Sig}
      {M M' : Γ ⊢U: X ! Σ}
      {N N' : Γ ∷ X ⊢U: Y ! Σ}
      → Γ ⊢U M ≡ M'
      → Γ ∷ X ⊢U N ≡ N'
      --------------------
      → Γ ⊢U `let M `in N ≡ `let M' `in N'

    match-with-cong :
      {X Y : VType} {Xᵤ : UType}
      {V V' : Γ ⊢V: X ×v Y}
      {M M' : Γ ∷ X ∷ Y ⊢U: Xᵤ}
      → Γ ⊢V V ≡ V'
      → Γ ∷ X ∷ Y ⊢U M ≡ M'
      ----------------------
      → Γ ⊢U (match V `with M) ≡ (match V' `with M')


    using-at-run-finally-cong :
      {X Y : VType} {Σ Σ' : Sig} {C : KState}
      {V V' : Γ ⊢V: Σ ⇒ Σ' , C}
      {W W' : Γ ⊢V: gnd C}
      {M M' : Γ ⊢U: X ! Σ}
      {N N' : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ'}
      → Γ ⊢V V ≡ V'
      → Γ ⊢V W ≡ W'
      → Γ ⊢U M ≡ M'
      → Γ ∷ X ∷ gnd C ⊢U N ≡ N'
      ------------------------
      → Γ ⊢U `using V at W `run M finally N
      ≡ `using V' at W' `run M' finally N'

    kernel-at-finally-cong :
      {X Y : VType} {Σ : Sig} {C : KState}
      {V V' : Γ ⊢V: gnd C}
      {M M' : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ}
      {K K' : Γ ⊢K: X ↯ Σ , C}
      → Γ ⊢V V ≡ V'
      → Γ ∷ X ∷ gnd C ⊢U M ≡ M'
      → Γ ⊢K K ≡ K'
      ------------------------
      → Γ ⊢U kernel K at V finally M ≡ kernel K' at V' finally M'

    -- rules from the paper
    funU-beta : {X : VType} {Xᵤ : UType} -- str32 prva vrstica
      → (M : (Γ ∷ X) ⊢U: Xᵤ)
      → (V : Γ ⊢V: X)
      -------------------------------
      → Γ ⊢U (funU M) · V ≡ (M [ idₛ ∷ₛ V ]ᵤ)

    let-in-beta-return_ : {X Y : VType} {Σ : Sig}
      → (V : Γ ⊢V: X)
      → (M : Γ ∷ X ⊢U: Y ! Σ)
      ----------------------------
      → Γ ⊢U `let (return V) `in M ≡ (M [ (idₛ ∷ₛ V) ]ᵤ)

    let-in-beta-op : {X Y : VType} {Σ : Sig}
      → (op : Op)
      → (x : op ∈ₒ Σ)
      → (V : Γ ⊢V: gnd (param op))
      → (M : Γ ∷ gnd (result op) ⊢U: X ! Σ)
      → (N : Γ ∷ X ⊢U: Y ! Σ)
      --------------------------------
      → Γ ⊢U `let (opᵤ op x V M) `in N ≡ 
        opᵤ op x V (`let M `in (N [ extdᵣ wkᵣ ]ᵤᵣ))

    match-with-beta-prod : {X Y : VType} {Xᵤ : UType}
      (V : Γ ⊢V: X)
      (W : Γ ⊢V: Y)
      → (M : Γ ∷ X ∷ Y ⊢U: Xᵤ)
      -----------------
      → Γ ⊢U match ⟨ V , W ⟩ `with M ≡ (M [ ((idₛ ∷ₛ V) ∷ₛ W) ]ᵤ)

    using-run-finally-beta-return :
      {Σ Σ' : Sig} {C : KState} {X Y : VType}
      → (R : Γ ⊢V: Σ ⇒ Σ' , C)
      → (W : Γ ⊢V: gnd C)
      → (V : Γ ⊢V: X)
      → (N : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ')
      ------------
      → Γ ⊢U `using R at W `run return V finally N ≡ (N [ (idₛ ∷ₛ V) ∷ₛ W ]ᵤ)

    using-run-finally-beta-op :
      {Σ Σ' : Sig} {C : KState} {X Y : VType}
      → (R : ((op : Op) → (op ∈ₒ Σ) → co-op Γ Σ' C op))
      → (W : Γ ⊢V: gnd C)
      → (op : Op)
      → (V : Γ ⊢V: gnd (param op))
      → (x : op ∈ₒ Σ)
      → (M : Γ ∷ gnd (result op) ⊢U: X ! Σ)
      → (N : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ')
      ------------
      → Γ ⊢U `using runner R at W `run (opᵤ op x V M) finally N
          ≡ kernel R op x [ idₛ ∷ₛ V ]ₖ at W finally 
            (`using (runner (rename-runner R (wkᵣ ∘ᵣ wkᵣ))) 
              at var here `run M [ wkᵣ ]ᵤᵣ finally 
                (N [ extdᵣ (extdᵣ (wkᵣ ∘ᵣ wkᵣ)) ]ᵤᵣ))

    kernel-at-finally-beta-return : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (V : Γ ⊢V: X)
      → (W : Γ ⊢V: gnd C)
      → (N : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ)
      -------------------
      → Γ ⊢U kernel return V at W finally N ≡ (N [ ((idₛ ∷ₛ V) ∷ₛ W) ]ᵤ)

    kernel-at-finally-beta-getenv : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (V : Γ ⊢V: gnd C)
      → (K : Γ ∷ gnd C ⊢K: X ↯ Σ , C)
      → (M : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ)
      -------------------
      → Γ ⊢U kernel getenv K at V finally M
          ≡ kernel K [ (idₛ ∷ₛ V) ]ₖ at V finally M

    kernel-at-finally-setenv : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (V W : Γ ⊢V: gnd C)
      → (K : Γ ⊢K: X ↯ Σ , C)
      → (M : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ)
      -------------------
      → Γ ⊢U kernel setenv V K at W finally M
          ≡ kernel K at V finally M

    kernel-at-finally-beta-op : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (op : Op)
      → (x : op ∈ₒ Σ)
      → (V : Γ ⊢V: gnd (param op))
      → (W : Γ ⊢V: gnd C)
      → (K : Γ ∷ gnd (result op) ⊢K: X ↯ Σ , C)
      → (M : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ)
      -------------------
      → Γ ⊢U kernel (opₖ op x V K) at W finally M ≡ 
          opᵤ op x V (kernel K at (W [ wkᵣ ]ᵥᵣ) finally 
            (M [ extdᵣ (extdᵣ wkᵣ) ]ᵤᵣ))

    let-in-eta-M : {X : VType}    -- let-eta
      {Σ : Sig}
      → (M : Γ ⊢U: X ! Σ)
      -------------------
      → Γ ⊢U `let M `in (return (var here)) ≡ M

  data _⊢K_≡_ where

    -- equivalence rules
    refl : {Xₖ : KType} {K : Γ ⊢K: Xₖ}
         ---------------------------
         → Γ ⊢K K ≡ K

    sym : {Xₖ : KType} {K  K' : Γ ⊢K: Xₖ}
      → Γ ⊢K K ≡ K'
      --------------------
      → Γ ⊢K K' ≡ K

    trans : {Xₖ : KType} { K K' K'' : Γ ⊢K: Xₖ}
      → Γ ⊢K K ≡ K'
      → Γ ⊢K K' ≡ K''
      --------------------------
      → Γ ⊢K K ≡ K''

    -- congruence rules

    return-cong :
      {X : VType} {Σ : Sig} {C : KState}
      {V₁ V₂ : Γ ⊢V: X}
      → Γ ⊢V V₁ ≡ V₂
      ----------------
      → Γ ⊢K return {Σ = Σ} {C = C} V₁ ≡ return V₂

    ·-cong :
      {X : VType} {Xₖ : KType}
      {V V' : Γ ⊢V: X ⟶ₖ Xₖ}
      {W W' : Γ ⊢V: X}
      → Γ ⊢V V ≡ V'
      → Γ ⊢V W ≡ W'
      -----------------------
      → Γ ⊢K (V · W) ≡ (V' · W')

    let-in-cong :
      {X Y : VType} {Σ : Sig} {C : KState}
      {K K' : Γ ⊢K:  X ↯ Σ , C}
      {L L' : Γ ∷ X ⊢K: Y ↯ Σ , C}
      → Γ ⊢K K ≡ K'
      → Γ ∷ X ⊢K L ≡ L'
      ----------------
      → Γ ⊢K `let K `in L ≡ `let K' `in L'

    match-with-cong :
      {X Y : VType} {Xₖ : KType}
      {V V' : Γ ⊢V: X ×v Y}
      {K K' : Γ ∷ X ∷ Y ⊢K: Xₖ}
      → Γ ⊢V V ≡ V'
      → Γ ∷ X ∷ Y ⊢K K ≡ K'
      ----------------
      → Γ ⊢K match V `with K ≡ (match V' `with K')

    opₖ-cong :
      {X Y : VType} {Σ : Sig} {C : KState}
      {op : Op}
      {x : op ∈ₒ Σ}
      {V V' : Γ ⊢V: gnd (param op)}
      {K K' : Γ ∷ gnd (result op) ⊢K: X ↯ Σ , C}
      → Γ ⊢V V ≡ V'
      → Γ ∷ gnd (result op) ⊢K K ≡ K'
      ----------------
      → Γ ⊢K opₖ op x V K ≡ opₖ op x V' K'

    getenv-cong :
      {X : VType} {C : KState} {Σ : Sig}
      {K K' : Γ ∷ gnd C ⊢K: X ↯ Σ , C}
      → Γ ∷ gnd C ⊢K K ≡ K'
      -----------------
      → Γ ⊢K getenv K ≡ getenv K'

    setenv-cong :
      {X : VType} {C : KState} {Σ : Sig}
      {V V' : Γ ⊢V: gnd C}
      {K K' : Γ ⊢K: X ↯ Σ , C}
      → Γ ⊢V V ≡ V'
      → Γ ⊢K K ≡ K'
      --------------------
      → Γ ⊢K setenv V K ≡ setenv V' K'

    user-with-cong :
      {X Y : VType} {Σ : Sig} {C : KState}
      {M M' : Γ ⊢U: X ! Σ}
      {K K' : Γ ∷ X ⊢K: Y ↯ Σ , C}
      → Γ ⊢U M ≡ M'
      → Γ ∷ X ⊢K K ≡ K'
      -------------------
      → Γ ⊢K user M `with K ≡ user M' `with K'


    -- rules from the paper

    funK-beta : {X : VType} {Xₖ : KType}
      → (K : Γ ∷ X ⊢K: Xₖ)
      → (V : Γ ⊢V: X)
      -------------------
      → Γ ⊢K (funK K) · V ≡ (K [ idₛ ∷ₛ V ]ₖ)

    let-in-beta-return : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (V : Γ ⊢V: X)
      → (K : Γ ∷ X ⊢K: Y ↯ Σ , C )
      -----------------
      → Γ ⊢K `let (return V) `in K ≡ (K [ idₛ ∷ₛ V ]ₖ )

    let-in-beta-op :
      {X Y Z : VType}
      {Σ : Sig} {C : KState}
      → (op : Op)
      → (x : op ∈ₒ Σ)
      → (V : Γ ⊢V: gnd (param op))
      → (K : Γ ∷ gnd (result op) ⊢K: X ↯ Σ , C)
      → (L : Γ ∷ X ⊢K: Y ↯ Σ , C)
      -----------------
      → Γ ⊢K `let (opₖ op x V K) `in L ≡ 
          opₖ op x V (`let K `in (L [ extdᵣ wkᵣ ]ₖᵣ))

    let-in-beta-getenv : {X Y : VType}
      {C : KState} {Σ : Sig}
      → (K : Γ ∷ gnd C ⊢K: X ↯ Σ , C)
      → (L : Γ ∷ X ⊢K: Y ↯ Σ , C)
      -----------------
      → Γ ⊢K `let (getenv K) `in L
          ≡ getenv (`let K `in (L [ extdᵣ wkᵣ ]ₖᵣ))

    let-in-beta-setenv : {X Y : VType}
      {C : KState} {Σ : Sig}
      → (V : Γ ⊢V: gnd C)
      → (K : Γ ⊢K: X ↯ Σ , C)
      → (L : Γ ∷ X ⊢K: Y ↯ Σ , C)
      -----------------
      → Γ ⊢K `let (setenv V K) `in L
          ≡ setenv V (`let K `in L)

    match-with-beta-prod : {X Y Z : VType}
      {Σ : Sig} {C : KState}
      → (V : Γ ⊢V: X)
      → (W : Γ ⊢V: Y)
      → (K : Γ ∷ X ∷ Y ⊢K: Z ↯ Σ , C)
      -------------------
      → Γ ⊢K match ⟨ V , W ⟩ `with K ≡ (K [ (idₛ ∷ₛ V) ∷ₛ W ]ₖ)

    user-with-beta-return : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (V : Γ ⊢V: X)
      → (K : Γ ∷ X ⊢K: Y ↯ Σ , C)
      ----------------------
      → Γ ⊢K user return V `with K ≡ (K [ (idₛ ∷ₛ V) ]ₖ)

    user-with-beta-op : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (op : Op)
      → (x : op ∈ₒ Σ)
      → (V : Γ ⊢V: gnd (param op))
      → (M : Γ ∷ gnd (result op) ⊢U: X ! Σ)
      → (K : Γ ∷ X ⊢K: Y ↯ Σ , C)
      ----------------------
      → Γ ⊢K user (opᵤ op x V M) `with K
          ≡ opₖ op x V (user M `with (K [ extdᵣ wkᵣ ]ₖᵣ))

    let-in-eta-K : {X : VType}
      {Σ : Sig} {C : KState}
      → (K : Γ ⊢K: X ↯ Σ , C)
      -------------------
      → Γ ⊢K `let K `in (return (var here)) ≡ K

    GetSetenv : {C : KState} {X Y : VType} {Σ : Sig}
      → (K : Γ ⊢K: X ↯ Σ , C)
      -------------
      → Γ ⊢K getenv (setenv (var here) (K [ wkᵣ ]ₖᵣ)) ≡ K

    SetGetenv : {C : KState} {X : VType} {Σ : Sig}
      → (V : Γ ⊢V: gnd C)
      → (K : Γ ∷ gnd C ⊢K: X ↯ Σ , C)
      --------------
      → Γ ⊢K setenv V (getenv K) ≡ setenv V (K [ idₛ ∷ₛ V ]ₖ)

    SetSetenv : {C C' : KState} {X : VType} {Σ : Sig}
      → (V W : Γ ⊢V: gnd C)
      → (K : Γ ⊢K: X ↯ Σ , C)
      --------------
      → Γ ⊢K setenv V (setenv W K) ≡ setenv W K

    GetOpEnv : {X Y : VType} {C  : KState} {Σ : Sig}
      → (op : Op)
      → (x : op ∈ₒ Σ)
      → (V : Γ ⊢V: gnd (param op))
      → (K : Γ ⊢K: X ↯ Σ , C)
      -----------------
      → Γ ⊢K getenv (opₖ op x (V [ wkᵣ ]ᵥᵣ) (K [ wkᵣ ∘ᵣ wkᵣ ]ₖᵣ)) ≡ 
          opₖ op x V (getenv (K [ wkᵣ ∘ᵣ wkᵣ ]ₖᵣ))

    SetOpEnv : {X : VType} {C : KState} {Σ : Sig}
      → (op : Op)
      → (x : op ∈ₒ Σ)
      → (W : Γ ⊢V: gnd C)
      → (V : Γ ⊢V: gnd (param op))
      → (K : Γ ∷ gnd (result op) ⊢K: X ↯ Σ , C)
      ----------------
      → Γ ⊢K setenv W (opₖ op x V K) ≡ 
        opₖ op x V (setenv (W [ wkᵣ ]ᵥᵣ) K)


infix 1 _⊢V_≡_ _⊢U_≡_ _⊢K_≡_
 