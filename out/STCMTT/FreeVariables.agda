module STCMTT.FreeVariables where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core

open import SOAS.Metatheory.MetaAlgebra

open import STCMTT.Signature
open import STCMTT.Syntax hiding (⅀F)

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; Σ-syntax)

module _ (𝔛 : Familyₛ {ΛT}) where

  ℱ𝒱 : Familyₛ {ΛT}
  ℱ𝒱 τ Γ = List (Σ[ α ∈ ΛT ] (ℐ α Γ))

  contract : {τ α : ΛT}{Γ : Ctx {ΛT}} → ℱ𝒱 τ (α ∙ Γ) → ℱ𝒱 τ Γ
  contract [] = []
  contract {τ} ((fst , new) ∷ xs) = contract {τ} xs
  contract {τ} ((fst , old snd) ∷ xs) = (fst , snd) ∷ (contract {τ} xs)

  mvarThing : {τ : ΛT}{Δ : Ctx {ΛT}} → (Γ : Ctx {ΛT}) → (Γ ~[ ℱ𝒱 ]↝ Δ) → ℱ𝒱 τ Δ
  mvarThing ∅ ε = []
  mvarThing {τ}{Δ} (α ∙ Γ) ε = (ε {α} new) ++ mvarThing {τ}{Δ} Γ (λ v → ε (old v))

  ℱ𝒱ᵃ : MetaAlg {ΛT} ⅀F 𝔛 [_]_ ℱ𝒱
  ℱ𝒱ᵃ = record {
      𝑎𝑙𝑔 = λ {τ : ΛT} → λ{ (appₒ ⋮ f , a) → f ++ a ; (lamₒ ⋮ b) → contract {Sort lamₒ} b }
    ; 𝑣𝑎𝑟 = λ {τ : ΛT} x → (τ , x) ∷ []
    ; 𝑚𝑣𝑎𝑟 = λ {τ : ΛT} {Γ : Ctx} 𝔪 {Δ : Ctx} ε → mvarThing {τ} Γ ε
    ; 𝑏𝑜𝑥 = λ x → [] }

  FV : Λ 𝔛 ⇾̣ ℱ𝒱
  FV = 𝕤𝕖𝕞 𝔛 ℱ𝒱ᵃ

