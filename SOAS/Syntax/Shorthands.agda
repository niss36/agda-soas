

open import SOAS.Common
open import SOAS.Families.Core
import SOAS.Context
import SOAS.Metatheory.MetaAlgebra

-- Shorthands for de Bruijn indices
module SOAS.Syntax.Shorthands {T : Set}
  (open SOAS.Context {T})
  {⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ}
  ([_]_ : Ctx → T → T)
  (open SOAS.Metatheory.MetaAlgebra ⅀F [_]_)
  {𝓐 : Family₂}(𝓐ᵃ : MetaAlg 𝓐)
  where

open import SOAS.Families.Build
open import SOAS.ContextMaps.Inductive
open import SOAS.Variable
open import Data.Nat

open import Relation.Nullary.Decidable using (True; toWitness)

private
  variable
    α β γ δ υ : T
    Γ Δ : Ctx
    𝔐 : MCtx

module _ where
  open MetaAlg 𝓐ᵃ

  -- Refer to variables via de Bruijn numerals: e.g. ` 2 = 𝑣𝑎𝑟 (old (old new))
  len : Ctx → ℕ
  len ∅        =  ℕ.zero
  len (α ∙ Γ)  =  suc (len Γ)

  ix : {Γ : Ctx} → {n : ℕ} → (p : n < len Γ) → T
  ix {(α ∙ _)} {zero}    (s≤s z≤n)  =  α
  ix {(_ ∙ Γ)} {(suc n)} (s≤s p)    =  ix p

  deBruijn : ∀ {Γ} → {n : ℕ} → (p : n < len Γ) → ℐ (ix p) Γ
  deBruijn {_ ∙ _} {zero}    (s≤s z≤n)  =  new
  deBruijn {_ ∙ Γ} {(suc n)} (s≤s p)    =  old (deBruijn p)

  ′ : {Γ : Ctx}(n : ℕ){n∈Γ : True (suc n ≤? len Γ)} → 𝓐 𝔐 (ix (toWitness n∈Γ)) Γ
  ′ n {n∈Γ} = 𝑣𝑎𝑟 (deBruijn (toWitness n∈Γ))

  -- Explicit abbreviations for de Bruijn indices 0-4
  x₀ : 𝓐 𝔐 α (α ∙ Γ)
  x₀ = 𝑣𝑎𝑟 new
  x₁ : 𝓐 𝔐 β (α ∙ β ∙ Γ)
  x₁ = 𝑣𝑎𝑟 (old new)
  x₂ : 𝓐 𝔐 γ (α ∙ β ∙ γ ∙ Γ)
  x₂ = 𝑣𝑎𝑟 (old (old new))
  x₃ : 𝓐 𝔐 δ (α ∙ β ∙ γ ∙ δ ∙ Γ)
  x₃ = 𝑣𝑎𝑟 (old (old (old new)))
  x₄ : 𝓐 𝔐 υ (α ∙ β ∙ γ ∙ δ ∙ υ ∙ Γ)
  x₄ = 𝑣𝑎𝑟 (old (old (old (old new))))
