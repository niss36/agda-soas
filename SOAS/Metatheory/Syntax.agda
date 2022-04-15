import SOAS.Context

-- Syntax of a second-order language
module SOAS.Metatheory.Syntax {T : Set}
  (open SOAS.Context {T})
  ([_]_ : Ctx → T → T) where

open import SOAS.Families.Core {T}

open import SOAS.Common
open import Categories.Object.Initial
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive
open import SOAS.Coalgebraic.Strength
open import SOAS.Abstract.ExpStrength
open import SOAS.Metatheory.MetaAlgebra

-- Data characterising a second-order syntax:
-- * a signature endofunctor ⅀
-- * coalgebraic and exponential strength
-- * initial (⅀,𝔛)-meta-algebra for each 𝔛
-- + an inductive metavariable constructor for convenience
record Syntax : Set₁ where
  field
    ⅀F    : Functor 𝔽amiliesₛ 𝔽amiliesₛ
    ⅀:CS  : CompatStrengths ⅀F
    𝕋:Init : Initial (𝕄etaAlgebras ⅀F [_]_)
    mvarᵢ  : {𝔐 : MCtx}{τ : T}{Π Γ : Ctx} (open Initial 𝕋:Init)
          → (Π ⊩ τ ∈ 𝔐) → Sub (𝐶 ⊥ 𝔐) Π Γ → 𝐶 ⊥ 𝔐 τ Γ

  open Initial 𝕋:Init

  private
    variable
      α α₁ α₂ α₃ α₄ : T
      Γ Π Π₁ Π₂ Π₃ Π₄ : Ctx
      𝔐 : MCtx
    Tm : MCtx → Familyₛ
    Tm 𝔐 = 𝐶 ⊥ 𝔐
  --
  -- Shorthands for metavariables associated with a metavariable environment
  infix 100 𝔞⟨_ 𝔟⟨_ 𝔠⟨_ 𝔡⟨_ 𝔢⟨_
  infix 100 ◌ᵃ⟨_ ◌ᵇ⟨_ ◌ᶜ⟨_ ◌ᵈ⟨_ ◌ᵉ⟨_

  𝔞⟨_ : Sub (Tm (⁅ Π ⊩ₙ α ⁆ 𝔐)) Π Γ → Tm (⁅ Π ⊩ₙ α ⁆ 𝔐) α Γ
  𝔞⟨ ε = mvarᵢ ↓ ε

  𝔟⟨_ : Sub (Tm (⁅ Π₁ ⊩ₙ α₁ ⁆ ⁅ Π ⊩ₙ α ⁆ 𝔐)) Π Γ
      → Tm (⁅ Π₁ ⊩ₙ α₁ ⁆ ⁅ Π ⊩ₙ α ⁆ 𝔐) α Γ
  𝔟⟨ ε = mvarᵢ (↑ ↓) ε

  𝔠⟨_ : Sub (Tm (⁅ Π₂ ⊩ₙ α₂ ⁆ ⁅ Π₁ ⊩ₙ α₁ ⁆ ⁅ Π ⊩ₙ α ⁆ 𝔐))  Π Γ
      → Tm (⁅ Π₂ ⊩ₙ α₂ ⁆ ⁅ Π₁ ⊩ₙ α₁ ⁆ ⁅ Π ⊩ₙ α ⁆ 𝔐) α Γ
  𝔠⟨ ε = mvarᵢ (↑ ↑ ↓) ε

  𝔡⟨_ : Sub (Tm (⁅ Π₃ ⊩ₙ α₃ ⁆ ⁅ Π₂ ⊩ₙ α₂ ⁆ ⁅ Π₁ ⊩ₙ α₁ ⁆ ⁅ Π ⊩ₙ α ⁆ 𝔐)) Π Γ
      → Tm (⁅ Π₃ ⊩ₙ α₃ ⁆ ⁅ Π₂ ⊩ₙ α₂ ⁆ ⁅ Π₁ ⊩ₙ α₁ ⁆ ⁅ Π ⊩ₙ α ⁆ 𝔐) α Γ
  𝔡⟨ ε = mvarᵢ (↑ ↑ ↑ ↓) ε
  𝔢⟨_ : Sub (Tm (⁅ Π₄ ⊩ₙ α₄ ⁆ ⁅ Π₃ ⊩ₙ α₃ ⁆ ⁅ Π₂ ⊩ₙ α₂ ⁆ ⁅ Π₁ ⊩ₙ α₁ ⁆ ⁅ Π ⊩ₙ α ⁆ 𝔐)) Π Γ
      → Tm (⁅ Π₄ ⊩ₙ α₄ ⁆ ⁅ Π₃ ⊩ₙ α₃ ⁆ ⁅ Π₂ ⊩ₙ α₂ ⁆ ⁅ Π₁ ⊩ₙ α₁ ⁆ ⁅ Π ⊩ₙ α ⁆ 𝔐) α Γ
  𝔢⟨ ε = mvarᵢ (↑ ↑ ↑ ↑ ↓) ε

  -- Shorthands for metavariables with an empty metavariable environment
  𝔞 : Tm (⁅ α ⁆ 𝔐) α Γ
  𝔞 = 𝔞⟨ •
  𝔟 : Tm (⁅ Π₁ ⊩ₙ α₁ ⁆ ⁅ α ⁆ 𝔐) α Γ
  𝔟 = 𝔟⟨ •
  𝔠 : Tm (⁅ Π₂ ⊩ₙ α₂ ⁆ ⁅ Π₁ ⊩ₙ α₁ ⁆ ⁅ α ⁆ 𝔐) α Γ
  𝔠 = 𝔠⟨ •
  𝔡 : Tm (⁅ Π₃ ⊩ₙ α₃ ⁆ ⁅ Π₂ ⊩ₙ α₂ ⁆ ⁅ Π₁ ⊩ₙ α₁ ⁆ ⁅ α ⁆ 𝔐) α Γ
  𝔡 = 𝔡⟨ •
  𝔢 : Tm (⁅ Π₄ ⊩ₙ α₄ ⁆ ⁅ Π₃ ⊩ₙ α₃ ⁆ ⁅ Π₂ ⊩ₙ α₂ ⁆ ⁅ Π₁ ⊩ₙ α₁ ⁆ ⁅ α ⁆ 𝔐) α Γ
  𝔢 = 𝔢⟨ •

  -- Synonyms for holes
  ◌ᵃ = 𝔞 ; ◌ᵇ = 𝔟 ; ◌ᶜ = 𝔠 ; ◌ᵈ = 𝔡 ; ◌ᵉ = 𝔢
  ◌ᵃ⟨_ = 𝔞⟨_ ; ◌ᵇ⟨_ = 𝔟⟨_ ; ◌ᶜ⟨_ = 𝔠⟨_ ; ◌ᵈ⟨_ = 𝔡⟨_ ; ◌ᵉ⟨_ = 𝔢⟨_
