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

exchᵣ : ∀ {Γ X Y} → Ren (Γ ∷ X ∷ Y) (Γ ∷ Y ∷ X)
exchᵣ here = there here
exchᵣ (there here) = here
exchᵣ (there (there x)) = there (there x)

extdᵣ : ∀ {Γ Γ' X} → Ren Γ' Γ → Ren (Γ' ∷ X) (Γ ∷ X)
extdᵣ ρ here = here
extdᵣ ρ (there p) = there (ρ p)

-- Action of renamings

interleaved mutual

  _[_]ᵥᵣ : ∀{Γ Γ' X} → Γ' ⊢V: X → Ren Γ Γ' → Γ ⊢V: X
  _[_]ᵤᵣ : ∀{Γ Γ' X} → Γ' ⊢U: X → Ren Γ Γ' → Γ ⊢U: X
  _[_]ₖᵣ : ∀{Γ Γ' X} → Γ' ⊢K: X → Ren Γ Γ' → Γ ⊢K: X

  rename-funK : ∀ {Γ Γ' X xₖ } → Γ ⊢V: X ⟶ₖ xₖ → Ren Γ' Γ → Γ' ⊢V: X ⟶ₖ xₖ 
  rename-funK (var x) ρ = var (ρ x)
  rename-funK (sub-value V p) ρ = sub-value (V [ ρ ]ᵥᵣ) p
  rename-funK (funK K) ρ = funK (K [ extdᵣ ρ ]ₖᵣ)

  -- Value
  -- Explanation: This auxilliary function is used to use renamings within the co-op construct
  rename-coop : ∀ { Γ Γ' Σ C op} → co-op Γ Σ C op → Ren Γ' Γ → co-op Γ' Σ C op -- This might be doable in a less brute force way
  rename-coop (sub-kernel k p) ρ = sub-kernel (k [ extdᵣ ρ ]ₖᵣ) p
  rename-coop (return v) ρ = return (v [ extdᵣ ρ ]ᵥᵣ)
  rename-coop (v · u) ρ = rename-funK v (extdᵣ ρ) · (u [ extdᵣ ρ ]ᵥᵣ)
  rename-coop (`let k `in l) ρ = `let k [ extdᵣ ρ ]ₖᵣ `in (l [ extdᵣ (extdᵣ ρ) ]ₖᵣ)
  rename-coop (match v `with k) ρ = match v [ extdᵣ ρ ]ᵥᵣ `with (k [ extdᵣ (extdᵣ (extdᵣ ρ)) ]ₖᵣ)
  rename-coop (opₖ op p v k) ρ = opₖ op p (v [ extdᵣ ρ ]ᵥᵣ) (k [ extdᵣ (extdᵣ ρ) ]ₖᵣ)
  rename-coop (getenv k) ρ = getenv (k [ extdᵣ (extdᵣ ρ) ]ₖᵣ)
  rename-coop (setenv v k) ρ = setenv (v [ extdᵣ ρ ]ᵥᵣ) (k [ extdᵣ ρ ]ₖᵣ)
  rename-coop (user m `with k) ρ = user m [ extdᵣ ρ ]ᵤᵣ `with (k [ extdᵣ (extdᵣ ρ) ]ₖᵣ)

  rename-runner : ∀ { Γ Γ' Σ Σ' C} → ((op : Op) → op ∈ₒ Σ → co-op Γ Σ' C op) → Ren Γ' Γ → ((op : Op) → op ∈ₒ Σ → co-op Γ' Σ' C op)
  rename-runner R ρ op p = rename-coop (R op p) ρ

  var p [ ρ ]ᵥᵣ = var (ρ p)
  sub-value v p [ ρ ]ᵥᵣ = sub-value ( v [ ρ ]ᵥᵣ) p
  ⟨⟩ [ ρ ]ᵥᵣ = ⟨⟩
  ⟨ v , w ⟩ [ ρ ]ᵥᵣ = ⟨  v [ ρ ]ᵥᵣ , w [ ρ ]ᵥᵣ ⟩
  (funU m) [ ρ ]ᵥᵣ = funU (m [ extdᵣ ρ ]ᵤᵣ) -- EXPLANATION: We know that ρ won't change the funU constructor, so we can simply use the action of ρ on M
                                           -- with the addition of an extra variable as a function adds that
  (funK k) [ ρ ]ᵥᵣ = funK (k [ extdᵣ ρ ]ₖᵣ)
  runner r [ ρ ]ᵥᵣ = runner (rename-runner r ρ)

  -- User
  sub-user m p [ ρ ]ᵤᵣ = sub-user (m [ ρ ]ᵤᵣ) p
  return v [ ρ ]ᵤᵣ = return (v [ ρ ]ᵥᵣ)
  (v₁ · v₂) [ ρ ]ᵤᵣ = (v₁ [ ρ ]ᵥᵣ) · (v₂ [ ρ ]ᵥᵣ)
  opᵤ op p v m [ ρ ]ᵤᵣ = opᵤ op p (v [ ρ ]ᵥᵣ) (m [ extdᵣ ρ ]ᵤᵣ)
  `let m `in n [ ρ ]ᵤᵣ = `let m [ ρ ]ᵤᵣ `in (n [ extdᵣ ρ ]ᵤᵣ )
  (match m `with n) [ ρ ]ᵤᵣ = match m [ ρ ]ᵥᵣ `with (n [ extdᵣ (extdᵣ ρ) ]ᵤᵣ)
  `using m at n `run k finally l [ ρ ]ᵤᵣ = `using m [ ρ ]ᵥᵣ at n [ ρ ]ᵥᵣ `run k [ ρ ]ᵤᵣ finally (l [ extdᵣ (extdᵣ ρ) ]ᵤᵣ)
  kernel k at m finally n [ ρ ]ᵤᵣ = kernel k [ ρ ]ₖᵣ at m [ ρ ]ᵥᵣ finally (n [ extdᵣ (extdᵣ ρ) ]ᵤᵣ)

  -- Kernel
  sub-kernel k p [ ρ ]ₖᵣ = sub-kernel (k [ ρ ]ₖᵣ) p
  return v [ ρ ]ₖᵣ = return (v [ ρ ]ᵥᵣ)
  (v · u) [ ρ ]ₖᵣ = rename-funK v ρ · (u [ ρ ]ᵥᵣ) -- rename-funK necessary here, because I do not know how to prove anything about Γ ⊢V: X ⟶ₖ Y
  `let k `in l [ ρ ]ₖᵣ = `let k [ ρ ]ₖᵣ `in (l [ extdᵣ ρ ]ₖᵣ)
  match v `with k [ ρ ]ₖᵣ = match v [ ρ ]ᵥᵣ `with (k [ extdᵣ (extdᵣ ρ) ]ₖᵣ)
  opₖ op p v k [ ρ ]ₖᵣ = opₖ op p (v [ ρ ]ᵥᵣ) (k [ extdᵣ ρ ]ₖᵣ)
  getenv k [ ρ ]ₖᵣ = getenv (k [ extdᵣ ρ ]ₖᵣ)
  setenv v k [ ρ ]ₖᵣ = setenv (v [ ρ ]ᵥᵣ) (k [ ρ ]ₖᵣ)
  user m `with k [ ρ ]ₖᵣ = user m [ ρ ]ᵤᵣ `with (k [ extdᵣ ρ ]ₖᵣ)
 