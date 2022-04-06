module SOAS.FreeVariables {T : Set} where

open import SOAS.Common
open import SOAS.Variable
open import SOAS.Context {T}
open import SOAS.Families.Core {T}

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; Σ-syntax)

ℱ𝒱 : Familyₛ
ℱ𝒱 τ Γ = List (Σ[ α ∈ T ] (ℐ α Γ))

contract¹ : {τ α : T}{Γ : Ctx} → ℱ𝒱 τ (α ∙ Γ) → ℱ𝒱 τ Γ
contract¹ [] = []
contract¹ {τ} ((fst , new) ∷ xs) = contract¹ {τ} xs
contract¹ {τ} ((fst , old snd) ∷ xs) = (fst , snd) ∷ (contract¹ {τ} xs)

contractⁿ : {τ : T}{Γ : Ctx} → (Θ : Ctx) → ℱ𝒱 τ (Θ ∔ Γ) → ℱ𝒱 τ Γ
contractⁿ ∅ fv = fv
contractⁿ {τ} (α ∙ Θ) fv = contractⁿ {τ} Θ (contract¹ {τ} fv)

mvarThing : {τ : T}{Δ : Ctx} → (Γ : Ctx) → (Γ ~[ ℱ𝒱 ]↝ Δ) → ℱ𝒱 τ Δ
mvarThing ∅ ε = []
mvarThing {τ}{Δ} (α ∙ Γ) ε = (ε {α} new) ++ mvarThing {τ}{Δ} Γ (λ v → ε (old v))

open import Categories.Object.Initial

open import SOAS.Syntax.Arguments {T}
open import SOAS.Syntax.Signature T

import SOAS.Metatheory.MetaAlgebra

module FreeVar
  (𝔛 : Familyₛ)
  ([_]_ : Ctx → T → T)
  {O : Set}(𝕋:Sig : Signature O)
  (open Signature 𝕋:Sig)
  (open SOAS.Metatheory.MetaAlgebra {T} ⅀F 𝔛 [_]_)
  (𝕋:Init : Initial 𝕄etaAlgebras) where

  open import SOAS.Abstract.ExpStrength
  open CompatStrengths ⅀:CompatStr
  open import SOAS.Metatheory.Semantics {T} [_]_ ⅀F CoalgStr 𝔛 𝕋:Init

  -- List (Ctx × T) should really be the last k elements of (Arity op), where k is the number of times we've recursed.
  -- Not sure if it matters though
  opThing : {Γ : Ctx} → (op : O) → (a : List (Ctx × T)) → Arg a ℱ𝒱 Γ → ℱ𝒱 (Sort op) Γ
  opThing op [] _ = []
  opThing op ((Θ , τ) ∷ []) fv = contractⁿ {Sort op} Θ fv
  opThing op ((Θ , τ) ∷ x ∷ as) (fv , args) = (contractⁿ {Sort op} Θ fv) ++ (opThing op (x ∷ as) args)

  ℱ𝒱ᵃ : MetaAlg ℱ𝒱
  ℱ𝒱ᵃ = record {
        𝑎𝑙𝑔 = λ{ (op ⋮ args) → opThing op (Arity op) args }
      ; 𝑣𝑎𝑟 = λ {τ : T} x → (τ , x) ∷ []
      ; 𝑚𝑣𝑎𝑟 = λ {τ : T} {Γ : Ctx} 𝔪 {Δ : Ctx} ε → mvarThing {τ} Γ ε
      ; 𝑏𝑜𝑥 = λ x → [] }

  open Semantics

  FV : 𝕋 ⇾̣ ℱ𝒱
  FV = 𝕤𝕖𝕞 ℱ𝒱ᵃ
