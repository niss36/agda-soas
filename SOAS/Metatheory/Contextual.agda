open import SOAS.Common
import SOAS.Context

-- Definitions for Contextual Modal Types
module SOAS.Metatheory.Contextual {T : Set}
  (open SOAS.Context {T})
  ([_]_ : Ctx → T → T) where

open import SOAS.Families.Core {T}

open import SOAS.Coalgebraic.Strength

module _ (Ψ : Ctx) where

  -- Context Replacement
  KF : Functor 𝔽amiliesₛ 𝔽amiliesₛ
  KF = record { F₀ = λ 𝒳 τ Γ → 𝒳 τ Ψ ; F₁ = λ f → f ; identity = refl ; homomorphism = refl ; F-resp-≈ = λ z → z }

  open Functor KF public using () renaming (F₀ to K ; F₁ to K₁)

  -- Box
  δboxF : Functor 𝔽amiliesₛ 𝔽amiliesₛ
  δboxF = record { F₀ = λ 𝒳 τ Γ → 𝒳 ([ Ψ ] τ) Γ ; F₁ = λ f → f ; identity = refl ; homomorphism = refl ; F-resp-≈ = λ z → z }

  open Functor δboxF public using () renaming (F₀ to δbox ; F₁ to δbox₁)

-- Letbox
LBF : Functor 𝔽amilies₂ 𝔽amilies₂
LBF = record
  { F₀ = λ 𝓧 𝔐 τ Γ → Σ[ Ψ ∈ Ctx ] Σ[ α ∈ T ] (𝓧 𝔐 ([ Ψ ] α) Γ × 𝓧 (⁅ Ψ ⊩ₙ α ⁆ 𝔐) τ Γ)
  ; F₁ = λ{ f (Ψ , α , fst , snd) → Ψ , α , f fst , f snd }
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ{ {f = f}{g = g} p {x = (Ψ , α , fst , snd)} → trans (cong (λ y → Ψ , α , y , f snd ) (p {x = fst})) (cong (λ y → Ψ , α , g fst , y) (p {x = snd})) }
  }

open Functor LBF public using () renaming (F₀ to LB ; F₁ to LB₁)
