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

    refl : {X : VType} {v : Γ ⊢V: X}
         ---------------------------
         → Γ ⊢V v ≡ v

    sym : {X : VType} {v v' : Γ ⊢V: X}
      → Γ ⊢V v ≡ v'
      --------------------
      → Γ ⊢V v' ≡ v

    trans : {X : VType} {v w z : Γ ⊢V: X}
      → Γ ⊢V v ≡ w
      → Γ ⊢V w ≡ z
      --------------------------
      → Γ ⊢V v ≡ z

    -- congruence rules

    prod-cong :
      {X Y : VType}
      {v₁ v₂ : Γ ⊢V: X}
      {w₁ w₂ : Γ ⊢V: Y}
      → Γ ⊢V v₁ ≡ v₂
      → Γ ⊢V w₁ ≡ w₂
      -----------------------------
      → Γ ⊢V ⟨ v₁ , w₁ ⟩ ≡ ⟨ v₂ , w₂ ⟩

    fun-cong :
        {X : VType} {Xᵤ : UType}
        {m n : Γ ∷ X ⊢U: Xᵤ}
      → (Γ ∷ X) ⊢U m ≡ n
      -------------------------
      → Γ ⊢V (funU m) ≡ (funU n)

    funK-cong :
      {X : VType} {Xₖ : KType}
      {m n : (Γ ∷ X) ⊢K: Xₖ}
      → (Γ ∷ X) ⊢K m ≡ n
      -----------------
      → Γ ⊢V (funK m) ≡ (funK n)

    runner-cong :
      {X : VType} {Σ Σ' : Sig} {C : KState}
      {r r' : ((op : Op) → (op ∈ₒ Σ) → co-op Γ Σ' C op)}
      → ((op : Op) → (p : op ∈ₒ Σ) → (Γ ∷ gnd (param op)) ⊢K r op p ≡ r' op p)
      ------------------------------------------------------------------------
      → Γ ⊢V runner r ≡ runner r'

    -- rules from the paper


    unit-eta : {v : Γ ⊢V: gnd unit}
           ----------------------
           → Γ ⊢V v ≡ ⟨⟩

    funU-eta : {X : VType} {Xᵤ : UType} --funU-eta
      {v : Γ ⊢V: X ⟶ᵤ Xᵤ}
      ------------
      → Γ ⊢V funU ((v [ wkᵣ ]ᵥᵣ) · var here) ≡ v -- str 32 fig 12 druga enačba v prvi vrstici

    funK-eta : {X : VType} {Xₖ : KType}
      {v : Γ ⊢V: X ⟶ₖ Xₖ}
      ---------------
      → Γ ⊢V funK ((v [ wkᵣ ]ᵥᵣ) · (var here)) ≡ v




  data _⊢U_≡_ where

    -- equivalence rules
    refl : {Xᵤ : UType} {m : Γ ⊢U: Xᵤ}
         ---------------------------
         → Γ ⊢U m ≡ m

    sym : {Xᵤ : UType} {m m' : Γ ⊢U: Xᵤ}
      → Γ ⊢U m ≡ m'
      --------------------
      → Γ ⊢U m' ≡ m

    trans : {Xᵤ : UType} { m m' m'' : Γ ⊢U: Xᵤ}
      → Γ ⊢U m ≡ m'
      → Γ ⊢U m' ≡ m''
      --------------------------
      → Γ ⊢U m ≡ m''

    -- congruence rules

    return-cong :
      {X : VType} {v w : Γ ⊢V: X}
      {Σ : Sig}
      → Γ ⊢V v ≡ w
      ------------------
      → Γ ⊢U return {Σ = Σ} v ≡ return w

    ·-cong :
      {X : VType} {Xᵤ : UType}
      {v₁ v₂ : Γ ⊢V: X ⟶ᵤ Xᵤ}
      {w₁ w₂ : Γ ⊢V: X}
      → Γ ⊢V v₁ ≡ v₂
      → Γ ⊢V w₁ ≡ w₂
      ----------------------
      → Γ ⊢U v₁ · w₁ ≡ (v₂ · w₂)

    opᵤ-cong :
      {X : VType} {Σ : Sig}
      {op : Op}
      {v₁ v₂ : Γ ⊢V: gnd (param op)}
      {m₁ m₂ : Γ ∷ gnd (result op) ⊢U: X ! Σ}
      → (p : op ∈ₒ Σ)
      → Γ ⊢V v₁ ≡ v₂
      → (Γ ∷ gnd (result op)) ⊢U m₁ ≡ m₂
      --------------------
      → Γ ⊢U opᵤ op p  v₁ m₁ ≡ opᵤ op p v₂ m₂

    let-in-cong :
      {X Y : VType} {Σ : Sig}
      {m₁ m₂ : Γ ⊢U: X ! Σ}
      {n₁ n₂ : Γ ∷ X ⊢U: Y ! Σ}
      → Γ ⊢U m₁ ≡ m₂
      → Γ ∷ X ⊢U n₁ ≡ n₂
      --------------------
      → Γ ⊢U `let m₁ `in n₁ ≡ `let m₂ `in n₂

    match-with-cong :
      {X Y : VType} {Xᵤ : UType}
      {v₁ v₂ : Γ ⊢V: X ×v Y}
      {m₁ m₂ : Γ ∷ X ∷ Y ⊢U: Xᵤ}
      → Γ ⊢V v₁ ≡ v₂
      → Γ ∷ X ∷ Y ⊢U m₁ ≡ m₂
      ----------------------
      → Γ ⊢U (match v₁ `with m₁) ≡ (match v₂ `with m₂)


    using-at-run-finally-cong :
      {X Y : VType} {Σ Σ' : Sig} {C : KState}
      {v₁ v₂ : Γ ⊢V: Σ ⇒ Σ' , C}
      {w₁ w₂ : Γ ⊢V: gnd C}
      {m₁ m₂ : Γ ⊢U: X ! Σ}
      {n₁ n₂ : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ'}
      → Γ ⊢V v₁ ≡ v₂
      → Γ ⊢V w₁ ≡ w₂
      → Γ ⊢U m₁ ≡ m₂
      → Γ ∷ X ∷ gnd C ⊢U n₁ ≡ n₂
      ------------------------
      → Γ ⊢U `using v₁ at w₁ `run m₁ finally n₁
      ≡ `using v₂ at w₂ `run m₂ finally n₂

    kernel-at-finally-cong :
      {X Y : VType} {Σ : Sig} {C : KState}
      {v₁ v₂ : Γ ⊢V: gnd C}
      {m₁ m₂ : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ}
      {k₁ k₂ : Γ ⊢K: X ↯ Σ , C}
      → Γ ⊢V v₁ ≡ v₂
      → Γ ∷ X ∷ gnd C ⊢U m₁ ≡ m₂
      → Γ ⊢K k₁ ≡ k₂
      ------------------------
      → Γ ⊢U kernel k₁ at v₁ finally m₁ ≡ kernel k₂ at v₂ finally m₂

    -- rules from the paper
    funU-beta : {X : VType} {Xᵤ : UType} -- str32 prva vrstica
      → (m : (Γ ∷ X) ⊢U: Xᵤ)
      → (v : Γ ⊢V: X)
      -------------------------------
      → Γ ⊢U (funU m) · v ≡ (m [ idₛ ∷ₛ v ]ᵤ)

    let-in-beta-return_ : {X Y : VType} {Σ : Sig}
      → (v : Γ ⊢V: X)
      → (m : Γ ∷ X ⊢U: Y ! Σ)
      ----------------------------
      → Γ ⊢U `let (return v) `in m ≡ (m [ (idₛ ∷ₛ v) ]ᵤ)

    let-in-beta-op : {X Y : VType} {Σ : Sig}
      → (op : Op)
      → (p : op ∈ₒ Σ)
      → (v : Γ ⊢V: gnd (param op))
      → (m : Γ ∷ gnd (result op) ⊢U: X ! Σ)
      → (n : Γ ∷ X ⊢U: Y ! Σ)
      --------------------------------
      → Γ ⊢U `let (opᵤ op p v m) `in n ≡ opᵤ op p v (`let m `in (n [ extdᵣ wkᵣ ]ᵤᵣ))

    match-with-beta-prod : {X Y : VType} {Xᵤ : UType}
      (v₁ : Γ ⊢V: X)
      (v₂ : Γ ⊢V: Y)
      → (m : Γ ∷ X ∷ Y ⊢U: Xᵤ)
      -----------------
      → Γ ⊢U match ⟨ v₁ , v₂ ⟩ `with m ≡ (m [ ((idₛ ∷ₛ v₁) ∷ₛ v₂) ]ᵤ)

    using-run-finally-beta-return :
      {Σ Σ' : Sig} {C : KState} {X Y : VType}
      → (r : Γ ⊢V: Σ ⇒ Σ' , C)
      → (w : Γ ⊢V: gnd C)
      → (v : Γ ⊢V: X)
      → (n : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ')
      ------------
      → Γ ⊢U `using r at w `run return v finally n ≡ (n [ (idₛ ∷ₛ v) ∷ₛ w ]ᵤ)

    using-run-finally-beta-op :
      {Σ Σ' : Sig} {C : KState} {X Y : VType}
      → (r : ((op : Op) → (op ∈ₒ Σ) → co-op Γ Σ' C op))
      → (w : Γ ⊢V: gnd C)
      → (op : Op)
      → (v : Γ ⊢V: gnd (param op))
      → (p : op ∈ₒ Σ)
      → (m : Γ ∷ gnd (result op) ⊢U: X ! Σ)
      → (n : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ')
      ------------
      → Γ ⊢U `using runner r at w `run (opᵤ op p v m) finally n
          ≡ kernel r op p [ idₛ ∷ₛ v ]ₖ at w finally (`using (runner (rename-runner r (wkᵣ ∘ᵣ wkᵣ))) 
              at var here `run m [ wkᵣ ]ᵤᵣ finally (n [ extdᵣ (extdᵣ (wkᵣ ∘ᵣ wkᵣ)) ]ᵤᵣ))

    kernel-at-finally-beta-return : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (v : Γ ⊢V: X)
      → (w : Γ ⊢V: gnd C)
      → (n : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ)
      -------------------
      → Γ ⊢U kernel return v at w finally n ≡ (n [ ((idₛ ∷ₛ v) ∷ₛ w) ]ᵤ)

    kernel-at-finally-beta-getenv : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (v : Γ ⊢V: gnd C)
      → (k : Γ ∷ gnd C ⊢K: X ↯ Σ , C)
      → (m : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ)
      -------------------
      → Γ ⊢U kernel getenv k at v finally m
          ≡ kernel k [ (idₛ ∷ₛ v) ]ₖ at v finally m

    kernel-at-finally-setenv : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (v w : Γ ⊢V: gnd C)
      → (k : Γ ⊢K: X ↯ Σ , C)
      → (m : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ)
      -------------------
      → Γ ⊢U kernel setenv v k at w finally m
          ≡ kernel k at v finally m

    kernel-at-finally-beta-op : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (op : Op)
      → (p : op ∈ₒ Σ)
      → (v : Γ ⊢V: gnd (param op))
      → (w : Γ ⊢V: gnd C)
      → (k : Γ ∷ gnd (result op) ⊢K: X ↯ Σ , C)
      → (m : Γ ∷ X ∷ gnd C ⊢U: Y ! Σ)
      -------------------
      → Γ ⊢U kernel (opₖ op p v k) at w finally m ≡ 
          opᵤ op p v (kernel k at (w [ wkᵣ ]ᵥᵣ) finally (m [ extdᵣ (extdᵣ wkᵣ) ]ᵤᵣ))
      --kernel (opₖ op p v k) at w finally m ≡ opᵤ op p v (kernel k at (w [ (wkₛ idₛ) ]ᵥ) finally (m [ extendₛ (extendₛ (wkₛ idₛ)) ]ᵤ))


    let-in-eta-M : {X : VType}    -- let-eta
      {Σ : Sig}
      → (m : Γ ⊢U: X ! Σ)
      -------------------
      → Γ ⊢U `let m `in (return (var here)) ≡ m

  data _⊢K_≡_ where

    -- equivalence rules
    refl : {Xₖ : KType} {k : Γ ⊢K: Xₖ}
         ---------------------------
         → Γ ⊢K k ≡ k

    sym : {Xₖ : KType} {k  k' : Γ ⊢K: Xₖ}
      → Γ ⊢K k ≡ k'
      --------------------
      → Γ ⊢K k' ≡ k

    trans : {Xₖ : KType} { k k' k'' : Γ ⊢K: Xₖ}
      → Γ ⊢K k ≡ k'
      → Γ ⊢K k' ≡ k''
      --------------------------
      → Γ ⊢K k ≡ k''

    -- congruence rules

    return-cong :
      {X : VType} {Σ : Sig} {C : KState}
      {v₁ v₂ : Γ ⊢V: X}
      → Γ ⊢V v₁ ≡ v₂
      ----------------
      → Γ ⊢K return {Σ = Σ} {C = C} v₁ ≡ return v₂

    ·-cong :
      {X : VType} {Xₖ : KType}
      {v₁ v₂ : Γ ⊢V: X ⟶ₖ Xₖ}
      {w₁ w₂ : Γ ⊢V: X}
      → Γ ⊢V v₁ ≡ v₂
      → Γ ⊢V w₁ ≡ w₂
      -----------------------
      → Γ ⊢K (v₁ · w₁) ≡ (v₂ · w₂)

    let-in-cong :
      {X Y : VType} {Σ : Sig} {C : KState}
      {k₁ k₂ : Γ ⊢K:  X ↯ Σ , C}
      {l₁ l₂ : Γ ∷ X ⊢K: Y ↯ Σ , C}
      → Γ ⊢K k₁ ≡ k₂
      → Γ ∷ X ⊢K l₁ ≡ l₂
      ----------------
      → Γ ⊢K `let k₁ `in l₁ ≡ `let k₂ `in l₂

    match-with-cong :
      {X Y : VType} {Xₖ : KType}
      {v₁ v₂ : Γ ⊢V: X ×v Y}
      {k₁ k₂ : Γ ∷ X ∷ Y ⊢K: Xₖ}
      → Γ ⊢V v₁ ≡ v₂
      → Γ ∷ X ∷ Y ⊢K k₁ ≡ k₂
      ----------------
      → Γ ⊢K match v₁ `with k₁ ≡ (match v₂ `with k₂)

    opₖ-cong :  -- cong pravilo, poglej še enkrat če pravilno
      {X Y : VType} {Σ : Sig} {C : KState}
      {op : Op}
      {p : op ∈ₒ Σ}
      {v₁ v₂ : Γ ⊢V: gnd (param op)}
      {k₁ k₂ : Γ ∷ gnd (result op) ⊢K: X ↯ Σ , C}
      → Γ ⊢V v₁ ≡ v₂
      → Γ ∷ gnd (result op) ⊢K k₁ ≡ k₂
      ----------------
      → Γ ⊢K opₖ op p v₁ k₁ ≡ opₖ op p v₂ k₂

    getenv-cong :
      {X : VType} {C : KState} {Σ : Sig}
      {k₁ k₂ : Γ ∷ gnd C ⊢K: X ↯ Σ , C}
      → Γ ∷ gnd C ⊢K k₁ ≡ k₂
      -----------------
      → Γ ⊢K getenv k₁ ≡ getenv k₂

    setenv-cong :
      {X : VType} {C : KState} {Σ : Sig}
      {v₁ v₂ : Γ ⊢V: gnd C}
      {k₁ k₂ : Γ ⊢K: X ↯ Σ , C}
      → Γ ⊢V v₁ ≡ v₂
      → Γ ⊢K k₁ ≡ k₂
      --------------------
      → Γ ⊢K setenv v₁ k₁ ≡ setenv v₂ k₂

    user-with-cong :
      {X Y : VType} {Σ : Sig} {C : KState}
      {m₁ m₂ : Γ ⊢U: X ! Σ}
      {k₁ k₂ : Γ ∷ X ⊢K: Y ↯ Σ , C}
      → Γ ⊢U m₁ ≡ m₂
      → Γ ∷ X ⊢K k₁ ≡ k₂
      -------------------
      → Γ ⊢K user m₁ `with k₁ ≡ user m₂ `with k₂


    -- rules from the paper

    funK-beta : {X : VType} {Xₖ : KType}
      → (k : Γ ∷ X ⊢K: Xₖ)
      → (v : Γ ⊢V: X)
      -------------------
      → Γ ⊢K (funK k) · v ≡ (k [ idₛ ∷ₛ v ]ₖ)

    let-in-beta-return : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (v : Γ ⊢V: X)
      → (k : Γ ∷ X ⊢K: Y ↯ Σ , C )
      -----------------
      → Γ ⊢K `let (return v) `in k ≡ (k [ idₛ ∷ₛ v ]ₖ )

    let-in-beta-op :
      {X Y Z : VType}
      {Σ : Sig} {C : KState}
      → (op : Op)
      → (p : op ∈ₒ Σ)
      → (v : Γ ⊢V: gnd (param op))
      → (k : Γ ∷ gnd (result op) ⊢K: X ↯ Σ , C)
      → (l : Γ ∷ X ⊢K: Y ↯ Σ , C)
      -----------------
      → Γ ⊢K `let (opₖ op p v k) `in l ≡ opₖ op p v (`let k `in (l [ extdᵣ wkᵣ ]ₖᵣ))

    let-in-beta-getenv : {X Y : VType} -- nisem povsem preprican tu
      {C : KState} {Σ : Sig}
      → (k : Γ ∷ gnd C ⊢K: X ↯ Σ , C)
      → (l : Γ ∷ X ⊢K: Y ↯ Σ , C)
      -----------------
      → Γ ⊢K `let (getenv k) `in l
          ≡ getenv (`let k `in (l [ extdᵣ wkᵣ ]ₖᵣ))

    let-in-beta-setenv : {X Y : VType}
      {C : KState} {Σ : Sig}
      → (v : Γ ⊢V: gnd C)
      → (k : Γ ⊢K: X ↯ Σ , C)
      → (l : Γ ∷ X ⊢K: Y ↯ Σ , C)
      -----------------
      → Γ ⊢K `let (setenv v k) `in l
          ≡ setenv v (`let k `in l)

    match-with-beta-prod : {X Y Z : VType}
      {Σ : Sig} {C : KState}
      → (v : Γ ⊢V: X)
      → (w : Γ ⊢V: Y)
      → (k : Γ ∷ X ∷ Y ⊢K: Z ↯ Σ , C)
      -------------------
      → Γ ⊢K match ⟨ v , w ⟩ `with k ≡ (k [ (idₛ ∷ₛ v) ∷ₛ w ]ₖ)

    {- match-with-beta-null : {X : VType}
      → {!!}
      -------------------
      → Γ ⊢K {!!} ≡ {!!} -}

    user-with-beta-return : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (v : Γ ⊢V: X)
      → (k : Γ ∷ X ⊢K: Y ↯ Σ , C)
      ----------------------
      → Γ ⊢K user return v `with k ≡ (k [ (idₛ ∷ₛ v) ]ₖ)

    user-with-beta-op : {X Y : VType}
      {Σ : Sig} {C : KState}
      → (op : Op)
      → (p : op ∈ₒ Σ)
      → (v : Γ ⊢V: gnd (param op))
      → (m : Γ ∷ gnd (result op) ⊢U: X ! Σ)
      → (k : Γ ∷ X ⊢K: Y ↯ Σ , C)
      ----------------------
      → Γ ⊢K user (opᵤ op p v m) `with k
          ≡ opₖ op p v (user m `with (k [ extdᵣ wkᵣ ]ₖᵣ))

    let-in-eta-K : {X : VType}
      {Σ : Sig} {C : KState}
      → (k : Γ ⊢K: X ↯ Σ , C)
      -------------------
      → Γ ⊢K `let k `in (return (var here)) ≡ k

    GetSetenv : {C : KState} {X Y : VType} {Σ : Sig} --tudi za pogledati
      → (k : Γ ⊢K: X ↯ Σ , C)
      -------------
      → Γ ⊢K getenv (setenv (var here) (k [ wkᵣ ]ₖᵣ)) ≡ k

    SetGetenv : {C : KState} {X : VType} {Σ : Sig}
      → (v : Γ ⊢V: gnd C)
      → (k : Γ ∷ gnd C ⊢K: X ↯ Σ , C)
      --------------
      → Γ ⊢K setenv v (getenv k) ≡ setenv v (k [ idₛ ∷ₛ v ]ₖ)

    SetSetenv : {C C' : KState} {X : VType} {Σ : Sig}
      → (v w : Γ ⊢V: gnd C)
      → (k : Γ ⊢K: X ↯ Σ , C)
      --------------
      → Γ ⊢K setenv v (setenv w k) ≡ setenv w k

    GetOpEnv : {X Y : VType} {C  : KState} {Σ : Sig}
      → (op : Op)
      → (p : op ∈ₒ Σ)
      → (v : Γ ⊢V: gnd (param op))
      → (k : Γ ⊢K: X ↯ Σ , C)
      -----------------
      → Γ ⊢K getenv (opₖ op p (v [ wkᵣ ]ᵥᵣ) (k [ wkᵣ ∘ᵣ wkᵣ ]ₖᵣ)) ≡ 
          opₖ op p v (getenv (k [ wkᵣ ∘ᵣ wkᵣ ]ₖᵣ))

    SetOpEnv : {X : VType} {C : KState} {Σ : Sig}
      → (op : Op)
      → (x : op ∈ₒ Σ)
      → (w : Γ ⊢V: gnd C)
      → (v : Γ ⊢V: gnd (param op))
      → (k : Γ ∷ gnd (result op) ⊢K: X ↯ Σ , C)
      ----------------
      → Γ ⊢K setenv w (opₖ op x v k) ≡ opₖ op x v (setenv (w [ wkᵣ ]ᵥᵣ) k)
      --setenv v (opₖ op x v k) ≡ opₖ op x v (setenv w k)
      --setenv v (opₖ op x v (k [ wkₛ idₛ ]ₖ)) ≡ opₖ op x v (setenv w (k [ wkₛ idₛ ]ₖ))


infix 1 _⊢V_≡_ _⊢U_≡_ _⊢K_≡_
  