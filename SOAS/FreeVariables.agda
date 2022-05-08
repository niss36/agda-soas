module SOAS.FreeVariables {T : Set} where

open import SOAS.Common
open import SOAS.Variable
open import SOAS.Context {T}
open import SOAS.Families.Core {T}

open import Data.List using (List; []; _∷_; _++_)

𝓕𝓥 : Family₂
𝓕𝓥 𝔐 τ Γ = List (Σ[ α ∈ T ] (ℐ α Γ))

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

open import Categories.Object.Initial

open import SOAS.Syntax.Arguments {T}
open import SOAS.Syntax.Signature T

import SOAS.Metatheory.MetaAlgebra

module FreeVar
  ([_]_ : Ctx → T → T)
  {O : Set}(𝕋:Sig : Signature O)
  (open Signature 𝕋:Sig)
  (open SOAS.Metatheory.MetaAlgebra {T} [_]_ ⅀F)
  (𝕋:Init : Initial 𝕄etaAlgebras) where

  open import SOAS.Abstract.ExpStrength
  open CompatStrengths ⅀:CompatStr
  open import SOAS.Metatheory.Semantics {T} [_]_ ⅀F CoalgStr 𝕋:Init

  -- List (Ctx × T) should really be the last k elements of (Arity op), where k is the number of times we've recursed.
  -- Not sure if it matters though
  opThing : {𝔐 : MCtx}{Γ : Ctx} → (op : O) → (a : List (Ctx × T)) → Arg a (𝓕𝓥 𝔐) Γ → 𝓕𝓥 𝔐 (Sort op) Γ
  opThing {𝔐} op [] _ = []
  opThing {𝔐} op ((Θ , τ) ∷ []) fv = contractⁿ {𝔐}{Sort op} Θ fv
  opThing {𝔐} op ((Θ , τ) ∷ x ∷ as) (fv , args) = (contractⁿ {𝔐}{Sort op} Θ fv) ++ (opThing {𝔐} op (x ∷ as) args)

  𝓕𝓥ᵃ : MetaAlg 𝓕𝓥
  𝓕𝓥ᵃ = record {
        𝑎𝑙𝑔 = λ {𝔐} → λ{ (op ⋮ args) → opThing {𝔐} op (Arity op) args }
      ; 𝑣𝑎𝑟 = λ {𝔐}{τ} x → (τ , x) ∷ []
      ; 𝑚𝑣𝑎𝑟 = λ {𝔐}{τ}{Γ} 𝔪 {Δ} ε → mvarThing {𝔐}{τ} Γ ε
      ; 𝑏𝑜𝑥 = λ x → [] }

  open Semantics

  FV : 𝕋 ⇾̣₂ 𝓕𝓥
  FV = 𝕤𝕖𝕞 𝓕𝓥ᵃ
