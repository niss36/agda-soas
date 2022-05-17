open import Categories.Object.Initial

import SOAS.Context
import SOAS.Syntax.Signature
import SOAS.Metatheory.MetaAlgebra

module SOAS.FreeVariables {T : Set}
  (open SOAS.Context {T})
  ([_]_ : Ctx → T → T)
  (open SOAS.Syntax.Signature T)
  {O : Set}(𝕋:Sig : Signature O)
  (open Signature 𝕋:Sig)
  (open SOAS.Metatheory.MetaAlgebra {T} [_]_ ⅀F)
  (𝕋:Init : Initial 𝕄etaAlgebras) where

open import SOAS.Common
open import SOAS.Variable
open import SOAS.Families.Core {T}

open import SOAS.Syntax.Arguments {T}

open import SOAS.Abstract.ExpStrength
open CompatStrengths ⅀:CompatStr
open import SOAS.Metatheory.Semantics {T} [_]_ ⅀F CoalgStr 𝕋:Init

open import Data.List using (List; []; _∷_; _++_; concat)

-- Maps the arguments for an operator to a list using the provided function
opArgsMap : {𝒳 : Familyₛ}{Γ : Ctx}
     → (op : O)
     → ((τ : T) → (Θ : Ctx) → 𝒳 τ (Θ ∔ Γ) → 𝒳 (Sort op) Γ) -- conversion function
     → (a : List (Ctx × T)) → Arg a 𝒳 Γ → List (𝒳 (Sort op) Γ)
opArgsMap op f [] _ = []
opArgsMap op f ((Θ , τ) ∷ []) x = (f τ Θ x) ∷ []
opArgsMap op f ((Θ , τ) ∷ y ∷ ys) (x , args) = (f τ Θ x) ∷ (opArgsMap op f (y ∷ ys) args)

-- Free Variables
module _ where

  𝓕𝓥 : Family₂
  𝓕𝓥 _ _ Γ = List (Σ[ α ∈ T ] (ℐ α Γ))

  contract¹ : {𝔐 : MCtx}{τ α : T}{Γ : Ctx} → 𝓕𝓥 𝔐 τ (α ∙ Γ) → 𝓕𝓥 𝔐 τ Γ
  contract¹ [] = []
  contract¹ {𝔐}{τ} ((fst , new) ∷ xs) = contract¹ {𝔐}{τ} xs
  contract¹ {𝔐}{τ} ((fst , old snd) ∷ xs) = (fst , snd) ∷ (contract¹ {𝔐}{τ} xs)

  contractⁿ : {𝔐 : MCtx}{τ : T}{Γ : Ctx} → (Θ : Ctx) → 𝓕𝓥 𝔐 τ (Θ ∔ Γ) → 𝓕𝓥 𝔐 τ Γ
  contractⁿ ∅ fv = fv
  contractⁿ {𝔐}{τ} (α ∙ Θ) fv = contractⁿ {𝔐}{τ} Θ (contract¹ {𝔐}{τ} fv)

  mvarThing : {𝔐 : MCtx}{τ : T}{Δ : Ctx} → (Γ : Ctx) → (Γ ~[ 𝓕𝓥 𝔐 ]↝ Δ) → 𝓕𝓥 𝔐 τ Δ
  mvarThing ∅ ε = []
  mvarThing {τ}{Δ} (α ∙ Γ) ε = (ε {α} new) ++ mvarThing {τ}{Δ} Γ (λ v → ε (old v))

  𝓕𝓥ᵃ : MetaAlg 𝓕𝓥
  𝓕𝓥ᵃ = record {
        𝑎𝑙𝑔 = λ {𝔐} → λ{ (op ⋮ args) → concat (opArgsMap op (λ _ → contractⁿ {𝔐}{Sort op}) (Arity op) args) }
      ; 𝑣𝑎𝑟 = λ {𝔐}{τ} x → (τ , x) ∷ []
      ; 𝑚𝑣𝑎𝑟 = λ {𝔐}{τ}{Γ} 𝔪 {Δ} ε → mvarThing {𝔐}{τ} Γ ε
      ; 𝑏𝑜𝑥 = λ x → []
      ; 𝑙𝑒𝑡𝑏𝑜𝑥 = λ{ {𝔐}{τ}{Γ} (Ψ , α , fst , snd) → fst ++ snd }
      }

  open Semantics

  FV : 𝕋 ⇾̣₂ 𝓕𝓥
  FV = 𝕤𝕖𝕞 𝓕𝓥ᵃ


-- Free Meta-Variables
module _ where

  𝓕𝓜𝓥 : Family₂
  𝓕𝓜𝓥 𝔐 _ _ = List (Σ[ α ∈ T ] Σ[ Δ ∈ Ctx ] (Δ ⊩ α ∈ 𝔐))

  mcontract¹ : {𝔐 : MCtx}{τ α : T}{Γ Ψ : Ctx} → 𝓕𝓜𝓥 (⁅ Ψ ⊩ₙ α ⁆ 𝔐) τ Γ → 𝓕𝓜𝓥 𝔐 τ Γ
  mcontract¹ [] = []
  mcontract¹ {τ}{α}{Γ}{Ψ} ((_ , _ , ↓) ∷ xs) = mcontract¹ {τ}{α}{Γ}{Ψ} xs
  mcontract¹ {τ}{α}{Γ}{Ψ} ((β , Δ , ↑ snd) ∷ xs) = (β , Δ , snd) ∷ (mcontract¹ {τ}{α}{Γ}{Ψ} xs)

  𝓕𝓜𝓥ᵃ : MetaAlg 𝓕𝓜𝓥
  𝓕𝓜𝓥ᵃ = record {
          𝑎𝑙𝑔 = λ {𝔐} → λ{ (op ⋮ args) → concat (opArgsMap op (λ _ _ x → x) (Arity op) args) }
        ; 𝑣𝑎𝑟 = λ x → []
        ; 𝑚𝑣𝑎𝑟 = λ {𝔐}{τ}{Γ} 𝔪 {Δ} ε → (τ , Γ , 𝔪) ∷ []
        ; 𝑏𝑜𝑥 = λ{ (Ψ , α , eq , x) → x }
        ; 𝑙𝑒𝑡𝑏𝑜𝑥 = λ{ {𝔐}{τ}{Γ} (Ψ , α , fst , snd) → fst ++ mcontract¹ {𝔐}{τ}{α}{Γ}{Ψ} snd }
        }

  open Semantics

  FMV : 𝕋 ⇾̣₂ 𝓕𝓜𝓥
  FMV = 𝕤𝕖𝕞 𝓕𝓜𝓥ᵃ
