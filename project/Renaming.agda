open import Parameters

module Renaming (G : GTypes) (O : Ops G) where

open import Types G O
open import Terms G O
open import Contexts G O

open GTypes G
open Ops O


-- Type of renamings

Ren : Ctx → Ctx → Set
Ren Γ Γ' = {X : VType} → X ∈ Γ' → X ∈ Γ

-- identity renaming

idᵣ : ∀ {Γ} → Ren Γ Γ
idᵣ x = x

-- composition of renamings

_∘ᵣ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
(ρ ∘ᵣ ρ') x = ρ' (ρ x)

-- weakening renaming

wkᵣ : ∀ {Γ X} → Ren (Γ ∷ X) Γ
wkᵣ x =  there x

-- exchange renaming

extdᵣ : ∀ {Γ Γ' X} → Ren Γ' Γ → Ren (Γ' ∷ X) (Γ ∷ X)
extdᵣ ρ here = here
extdᵣ ρ (there x) = there (ρ x)

-- Action of renamings

interleaved mutual

  _[_]ᵥᵣ : ∀{Γ Γ' X} → Γ' ⊢V: X → Ren Γ Γ' → Γ ⊢V: X
  _[_]ᵤᵣ : ∀{Γ Γ' X} → Γ' ⊢U: X → Ren Γ Γ' → Γ ⊢U: X
  _[_]ₖᵣ : ∀{Γ Γ' X} → Γ' ⊢K: X → Ren Γ Γ' → Γ ⊢K: X

  -- Value
  var x [ ρ ]ᵥᵣ = var (ρ x)
  sub-value V p [ ρ ]ᵥᵣ = sub-value (V [ ρ ]ᵥᵣ) p
  ⟨⟩ [ ρ ]ᵥᵣ = ⟨⟩
  ⟨ V , W ⟩ [ ρ ]ᵥᵣ = ⟨  V [ ρ ]ᵥᵣ , W [ ρ ]ᵥᵣ ⟩
  funU M [ ρ ]ᵥᵣ = funU (M [ extdᵣ ρ ]ᵤᵣ)
  funK K [ ρ ]ᵥᵣ = funK (K [ extdᵣ ρ ]ₖᵣ)
  runner R [ ρ ]ᵥᵣ = runner λ op x → (R op x [ extdᵣ ρ ]ₖᵣ)

  -- User
  sub-user M p [ ρ ]ᵤᵣ = sub-user (M [ ρ ]ᵤᵣ) p
  return V [ ρ ]ᵤᵣ = return (V [ ρ ]ᵥᵣ)
  (V · W) [ ρ ]ᵤᵣ = (V [ ρ ]ᵥᵣ) · (W [ ρ ]ᵥᵣ)
  opᵤ op p V M [ ρ ]ᵤᵣ = opᵤ op p (V [ ρ ]ᵥᵣ) (M [ extdᵣ ρ ]ᵤᵣ)
  `let M `in N [ ρ ]ᵤᵣ = `let M [ ρ ]ᵤᵣ `in (N [ extdᵣ ρ ]ᵤᵣ )
  (match M `with N) [ ρ ]ᵤᵣ = 
    match M [ ρ ]ᵥᵣ `with (N [ extdᵣ (extdᵣ ρ) ]ᵤᵣ)
  `using R at N `run K finally L [ ρ ]ᵤᵣ = 
    `using R [ ρ ]ᵥᵣ at N [ ρ ]ᵥᵣ 
      `run K [ ρ ]ᵤᵣ finally (L [ extdᵣ (extdᵣ ρ) ]ᵤᵣ)
  kernel K at M finally N [ ρ ]ᵤᵣ = 
    kernel K [ ρ ]ₖᵣ at M [ ρ ]ᵥᵣ finally (N [ extdᵣ (extdᵣ ρ) ]ᵤᵣ)

  -- Kernel
  sub-kernel K p [ ρ ]ₖᵣ = sub-kernel (K [ ρ ]ₖᵣ) p
  return V [ ρ ]ₖᵣ = return (V [ ρ ]ᵥᵣ)
  (V · W) [ ρ ]ₖᵣ = (V [ ρ ]ᵥᵣ) · (W [ ρ ]ᵥᵣ)
  `let K `in L [ ρ ]ₖᵣ = `let K [ ρ ]ₖᵣ `in (L [ extdᵣ ρ ]ₖᵣ)
  match V `with K [ ρ ]ₖᵣ = match V [ ρ ]ᵥᵣ `with (K [ extdᵣ (extdᵣ ρ) ]ₖᵣ)
  opₖ op x V K [ ρ ]ₖᵣ = opₖ op x (V [ ρ ]ᵥᵣ) (K [ extdᵣ ρ ]ₖᵣ)
  getenv K [ ρ ]ₖᵣ = getenv (K [ extdᵣ ρ ]ₖᵣ)
  setenv V K [ ρ ]ₖᵣ = setenv (V [ ρ ]ᵥᵣ) (K [ ρ ]ₖᵣ)
  user M `with K [ ρ ]ₖᵣ = user M [ ρ ]ᵤᵣ `with (K [ extdᵣ ρ ]ₖᵣ)
 