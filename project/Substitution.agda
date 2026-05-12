open import Parameters

module Substitution (G : GTypes) (O : Ops G) where

open import Types G O
open import Terms G O
open import Contexts G O
open import Renaming G O

open GTypes G
open Ops O

-- Type of substitutions

Sub : Ctx → Ctx → Set
Sub Γ Γ' = {X : VType} → X ∈ Γ' → Γ ⊢V: X

idₛ : ∀ {Γ} → Sub Γ Γ
idₛ = var

-- Auxiliary functions for substitutions

-- note: we probably should generalize this so that the extra variable (of type `X`)
--       maps to a given term, not necessarily itself
-- TASK: implement this one as two simpler functions:
--       (1) σ : Sub Γ Γ' is transformed to σ' : Sub (Γ ∷ X) Γ'
--       (2) given τ : Sub Δ Δ' and Δ ⊢ V : X, we get ⟨τ, V⟩ : Sub Δ (Δ' ∷ X)

--Composition of Renaming and Substitution
_ᵣ∘ₛ_ : ∀ {Γ Γ' Γ''} → Ren Γ Γ' → Sub Γ' Γ'' → Sub Γ Γ''
ρ ᵣ∘ₛ σ = λ x → σ x [ ρ ]ᵥᵣ

extendₛ : ∀ {Γ Γ' X} → Sub Γ Γ' → Sub (Γ ∷ X) (Γ' ∷ X)
extendₛ σ here = idₛ here
extendₛ σ (there x) =  σ x [ wkᵣ ]ᵥᵣ

wkₛ : ∀ {Γ Γ' X} → Sub Γ Γ' → Sub (Γ ∷ X) Γ'
wkₛ σ = (wkᵣ ᵣ∘ₛ σ)

_∷ₛ_ : ∀ {Γ Γ' X} → Sub Γ Γ' → Γ ⊢V: X → Sub Γ (Γ' ∷ X)
(σ ∷ₛ V) here = V
(σ ∷ₛ V) (there x) = σ x

--Composition of Substitution and Renaming
_ₛ∘ᵣ_ : ∀ {Γ Γ' Γ''} → Sub Γ Γ' → Ren Γ' Γ'' → Sub Γ Γ''
σ ₛ∘ᵣ ρ = λ x → σ (ρ x)


-- Action of substitutions

interleaved mutual

  _[_]ᵥ : ∀{Γ Γ' X} → Γ' ⊢V: X → Sub Γ Γ' → Γ ⊢V: X
  _[_]ᵤ : ∀{Γ Γ' X} → Γ' ⊢U: X → Sub Γ Γ' → Γ ⊢U: X
  _[_]ₖ : ∀{Γ Γ' X} → Γ' ⊢K: X → Sub Γ Γ' → Γ ⊢K: X

  -- Value
  var x [ σ ]ᵥ = σ x
  sub-value V p [ σ ]ᵥ = sub-value (V [ σ ]ᵥ) p
  ⟨⟩ [ σ ]ᵥ = ⟨⟩
  ⟨ V , W ⟩ [ σ ]ᵥ = ⟨ V [ σ ]ᵥ , W [ σ ]ᵥ ⟩
  (funU M) [ σ ]ᵥ = funU (M [ extendₛ σ ]ᵤ)
  (funK K) [ σ ]ᵥ = funK (K [ extendₛ σ ]ₖ)
  runner R [ σ ]ᵥ = runner λ op x → R op x [ extendₛ σ ]ₖ 

  -- User
  sub-user M p [ σ ]ᵤ = sub-user (M [ σ ]ᵤ) p
  return V [ σ ]ᵤ = return (V [ σ ]ᵥ)
  (V · W) [ σ ]ᵤ = (V [ σ ]ᵥ) · (W [ σ ]ᵥ)
  opᵤ op x V M [ σ ]ᵤ = opᵤ op x (V [ σ ]ᵥ) (M [ extendₛ σ ]ᵤ)
  `let M `in N [ σ ]ᵤ = `let M [ σ ]ᵤ `in (N [ (extendₛ σ) ]ᵤ)
  (match V `with M) [ σ ]ᵤ = match (V [ σ ]ᵥ) `with (M [ (extendₛ (extendₛ σ)) ]ᵤ)
  `using V at W `run M finally N [ σ ]ᵤ = 
    `using V [ σ ]ᵥ at W [ σ ]ᵥ `run M [ σ ]ᵤ finally (N [ extendₛ (extendₛ σ) ]ᵤ)
  kernel K at V finally M [ σ ]ᵤ = 
    kernel (K [ σ ]ₖ) at (V [ σ ]ᵥ) finally (M [ (extendₛ (extendₛ σ)) ]ᵤ)

  -- Kernel
  sub-kernel K p [ σ ]ₖ = sub-kernel (K [ σ ]ₖ) p
  return V [ σ ]ₖ = return (V [ σ ]ᵥ)
  (V · W) [ σ ]ₖ = (V [ σ ]ᵥ) · (W [ σ ]ᵥ)
  `let K `in L [ σ ]ₖ = `let (K [ σ ]ₖ) `in (L [ (extendₛ σ) ]ₖ)
  (match V `with K) [ σ ]ₖ = match V [ σ ]ᵥ `with (K [ (extendₛ (extendₛ σ)) ]ₖ)
  opₖ op x V K [ σ ]ₖ = opₖ op x (V [ σ ]ᵥ) (K [ extendₛ σ ]ₖ)
  getenv K [ σ ]ₖ = getenv (K [ (extendₛ σ) ]ₖ)
  setenv V K [ σ ]ₖ = setenv (V [ σ ]ᵥ) (K [ σ ]ₖ)
  user M `with K [ σ ]ₖ = user (M [ σ ]ᵤ) `with (K [ (extendₛ σ) ]ₖ)