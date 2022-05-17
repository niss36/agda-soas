open import SOAS.Common
import SOAS.Context

-- Definitions for Contextual Modal Types
module SOAS.Metatheory.Contextual {T : Set}
  (open SOAS.Context {T})
  ([_]_ : Ctx → T → T) where

open import SOAS.Families.Core {T}
open import SOAS.Variable {T}

open import SOAS.Coalgebraic.Strength
import SOAS.Abstract.Coalgebra as →□ ; open →□.Sorted
open import SOAS.Coalgebraic.Map {T}

module _ (Ψ : Ctx) where

  -- Context Replacement
  KF : Functor 𝔽amiliesₛ 𝔽amiliesₛ
  KF = record { F₀ = λ 𝒳 τ Γ → 𝒳 τ Ψ ; F₁ = λ f → f ; identity = refl ; homomorphism = refl ; F-resp-≈ = λ z → z }

  open Functor KF public using () renaming (F₀ to K ; F₁ to K₁)

  KF:Str : Strength KF
  KF:Str = record
    { str = λ 𝒫ᴮ 𝒳 x σ → x (Coalgₚ.η 𝒫ᴮ)
    ; str-nat₁ = λ fᴮ⇒ h σ → cong h (sym (dext λ {x} v → Coalgₚ⇒.⟨η⟩ fᴮ⇒))
    ; str-nat₂ = λ f h σ → refl
    ; str-unit = λ 𝒳 h → refl
    ; str-assoc = λ 𝒳 fᶜ h σ ς → cong h (sym (dext λ {x} v → Coalgebraic.f∘η fᶜ))
    }

  -- Box
  δboxF : Functor 𝔽amiliesₛ 𝔽amiliesₛ
  δboxF = record { F₀ = λ 𝒳 τ Γ → 𝒳 ([ Ψ ] τ) Γ ; F₁ = λ f → f ; identity = refl ; homomorphism = refl ; F-resp-≈ = λ z → z }

  open Functor δboxF public using () renaming (F₀ to δbox ; F₁ to δbox₁)

-- Box
BF : Functor 𝔽amiliesₛ 𝔽amiliesₛ
BF = record
  { F₀ = λ 𝓧 τ Γ → Σ[ Ψ ∈ Ctx ] Σ[ α ∈ T ] (τ ≡ [ Ψ ] α × 𝓧 α Ψ)
  ; F₁ = λ{ f (Ψ , α , eq , b) → Ψ , α , eq , f b }
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ{ p {x = (Ψ , α , fst , snd)} → cong (λ y → Ψ , α , fst , y) p }
  }

open Functor BF public using () renaming (F₀ to B ; F₁ to B₁)

BF:Str : Strength BF
BF:Str = record
  { str = λ{ 𝒫ᴮ 𝒳 (Ψ , α , eq , b) σ → Ψ , α , eq , b (Coalgₚ.η 𝒫ᴮ) }
  ; str-nat₁ = λ{ {𝒫 = 𝒫} fᴮ⇒ (Ψ , α , eq , b) σ → cong (λ (g : {τ : T} → ℐ τ Ψ → 𝒫 τ Ψ) → Ψ , α , eq , b g) (sym (dext λ {x} v → Coalgₚ⇒.⟨η⟩ fᴮ⇒)) }
  ; str-nat₂ = λ f h σ → refl
  ; str-unit = λ 𝒳 h → refl
  ; str-assoc = λ{ 𝒳 {ℛ = ℛ} fᶜ (Ψ , α , eq , b) σ ς → cong (λ (g : {τ : T} → ℐ τ Ψ → ℛ τ Ψ) → Ψ , α , eq , b g) (sym (dext λ {x} v → Coalgebraic.f∘η fᶜ)) }
  }

module BF:Str = Strength BF:Str

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
