open import Parameters

module Terms (G : GTypes) (O : Ops G) where

open import Types G O
open import Contexts G O

open GTypes G
open Ops O

-- Well-typed value and computation terms
interleaved mutual

  data _⊢V:_ (Γ : Ctx) : VType → Set
  data _⊢U:_ (Γ : Ctx) : UType → Set
  data _⊢K:_ (Γ : Ctx) : KType → Set

  -- Co-operations
  co-op : Ctx → Sig → KState → Op → Set
  co-op Γ Σ C op = Γ ∷ gnd (param op) ⊢K: gnd (result op) ↯ Σ , C

  data _⊢V:_ where

    var : {X : VType}
        → X ∈ Γ          -- constructively, exists a variable with type X in Γ
        -------------
        → Γ ⊢V: X

    sub-value : {X X' : VType}
        → Γ ⊢V: X
        → X ⊑ᵥ X'
        ------------------
        → Γ ⊢V: X'

    ⟨⟩ :
        --------------------
        Γ ⊢V: gnd unit

    ⟨_,_⟩ : {X Y : VType}
        → Γ ⊢V: X
        → Γ ⊢V: Y
        -------------------
        → Γ ⊢V: X ×v Y

    funU : {X : VType} {Xᵤ : UType}
          → Γ ∷ X ⊢U: Xᵤ
          ---------------------
          → Γ ⊢V: X ⟶ᵤ Xᵤ

    funK : {X : VType} {Xₖ : KType}
          → Γ ∷ X ⊢K: Xₖ
          ------------------------------
          → Γ ⊢V: X ⟶ₖ Xₖ

    runner : {Σ Σ' : Sig} {C : KState}
          → ((op : Op) → (op ∈ₒ Σ) → co-op Γ Σ' C op)
          ---------------------------------------------
          → Γ ⊢V: Σ ⇒ Σ' , C

  data _⊢U:_ where

    sub-user : {Xᵤ Xᵤ' : UType}
          → Γ ⊢U: Xᵤ
          → Xᵤ ⊑ᵤ Xᵤ'
          -----------------------
          → Γ ⊢U: Xᵤ'

    return : {X : VType} {Σ : Sig}
    -- TyUser-Return
        → Γ ⊢V: X
        ----------
        → Γ ⊢U: X ! Σ

    _·_ : {X : VType} {Xᵤ : UType} -- Formerly apply
      → Γ ⊢V: X ⟶ᵤ Xᵤ
      → Γ ⊢V: X
      -------------------------
      → Γ ⊢U: Xᵤ

    opᵤ : {X : VType} {Σ : Sig}
        → (op : Op)
        → op ∈ₒ Σ
        → Γ ⊢V: gnd (param op)
        → Γ ∷ gnd (result op) ⊢U: X ! Σ
        -------------------------------
        → Γ ⊢U: X ! Σ

    `let_`in : {X Y : VType} { Σ : Sig }
      → Γ ⊢U: X ! Σ
      → Γ ∷ X ⊢U: Y ! Σ
      ----------
      → Γ ⊢U: Y ! Σ

    match_`with : {X Y : VType} {Xᵤ : UType}
      → Γ ⊢V: X ×v Y
      → Γ ∷ X ∷ Y ⊢U: Xᵤ
      ----------------------------
      → Γ ⊢U: Xᵤ

    `using_at_`run_finally : {Σ Σ' : Sig} {C : KState} {X Y : VType}
      → Γ ⊢V: Σ ⇒ Σ' , C
      → Γ ⊢V: gnd C
      → Γ ⊢U: X ! Σ
      → Γ ∷ X ∷ gnd C ⊢U: Y ! Σ'
      -----------------
      → Γ ⊢U: Y ! Σ'

    kernel_at_finally :{X Y : VType} {Σ : Sig} {C : KState}
      → Γ ⊢K: X ↯ Σ , C
      → Γ ⊢V: gnd C
      → Γ ∷ X ∷ gnd C ⊢U: Y ! Σ
      --------------
      → Γ ⊢U: Y ! Σ

  data _⊢K:_ where

    sub-kernel : {Xₖ Xₖ' : KType}
          → Γ ⊢K: Xₖ
          → Xₖ ⊑ₖ Xₖ'
          ------------------------------------
          → Γ ⊢K: Xₖ'

    return : {X : VType} {Σ : Sig} {C : KState}
      → Γ ⊢V: X
      --------------------------
      → Γ ⊢K: X ↯ Σ , C

    _·_ : {X : VType} {Xₖ : KType}
      → Γ ⊢V: X ⟶ₖ Xₖ
      → Γ ⊢V: X
      ---------------------------------
      → Γ ⊢K: Xₖ

    `let_`in : {X Y : VType} {Σ : Sig} {C : KState}
      → Γ ⊢K: X ↯ Σ , C
      → Γ ∷ X ⊢K: Y ↯ Σ , C
      ---------------------------
      → Γ ⊢K: Y ↯ Σ , C

    match_`with : {X Y : VType} {Xₖ : KType}
      → Γ ⊢V: X ×v Y
      → Γ ∷ X ∷ Y ⊢K: Xₖ
      ---------------------
      → Γ ⊢K: Xₖ

    opₖ : {X : VType} {Σ : Sig} {C : KState}
      → (op : Op)
      → op ∈ₒ Σ
      → Γ ⊢V: gnd (param op)
      → Γ ∷ gnd (result op) ⊢K: X ↯ Σ , C
      ------------------------------
      → Γ ⊢K: X ↯ Σ , C

    getenv : {C : KState} {X : VType} {Σ : Sig}
      → Γ ∷ gnd C ⊢K: X ↯ Σ , C
      ---------------------------
      → Γ ⊢K: X ↯ Σ , C

    setenv : {C : KState} {X : VType} {Σ : Sig}
      → Γ ⊢V: gnd C
      → Γ ⊢K: X ↯ Σ , C
      -------------------------
      → Γ ⊢K: X ↯ Σ , C

    user_`with : {Σ : Sig} {C : KState} {X Y : VType}
      → Γ ⊢U: X ! Σ
      → Γ ∷ X ⊢K: Y ↯ Σ , C
      --------------------------
      → Γ ⊢K: Y ↯ Σ , C


infix 1 _⊢U:_ _⊢K:_ _⊢V:_
