open import SOAS.Common

open import Data.Nat
open import Data.Nat.Show renaming (show to showNat)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Extrema.Nat
open import Data.String using (String; _++_) renaming (intersperse to join)

import SOAS.Context

module SOAS.PrettyPrint {T : Set}
  (open SOAS.Context {T})
  (showCtx : ℕ → Ctx → String) where

open import SOAS.Variable
open import SOAS.Families.Core {T}
open import SOAS.Families.Build {T}

𝒫𝒫 : Familyₛ
𝒫𝒫 τ Γ = String × ℕ

len : Ctx → ℕ
len ∅ = ℕ.zero
len (α ∙ Γ) = suc (len Γ)

open import Categories.Object.Initial

open import SOAS.Syntax.Arguments {T}
open import SOAS.Syntax.Signature T

open import SOAS.Metatheory.MetaAlgebra {T}

module PrettyPrint
  (𝔛 : Familyₛ)
  {𝔐 : MCtx}{eq : {τ : T}{Γ : Ctx} → 𝔛 τ Γ ≡ ∥ 𝔐 ∥ τ Γ}
  ([_]_ : Ctx → T → T)
  {O : Set}(𝕋:Sig : Signature O)
  (showOp : O → String)
  (open Signature 𝕋:Sig)
  (𝕋:Init : (𝔛 : Familyₛ) → Initial (𝕄etaAlgebras ⅀F 𝔛 [_]_)) where

  open import SOAS.Abstract.ExpStrength
  open CompatStrengths ⅀:CompatStr
  open import SOAS.Metatheory.Semantics {T} [_]_ ⅀F CoalgStr 𝔛 (𝕋:Init 𝔛)

  -- Operators

  showBinder : ℕ → Ctx → String
  showBinder n ∅ = ""
  showBinder n (α ∙ Γ) = (showCtx n (α ∙ Γ)) ++ ". "

  ppAlgArgs : {Γ : Ctx} → (op : O) → (a : List (Ctx × T)) → Arg a 𝒫𝒫 Γ → 𝒫𝒫 (Sort op) Γ
  ppAlgArgs {Γ} op a args = join ", " (map proj₁ (aux {Γ} op a args)) , max ℕ.zero (map proj₂ (aux {Γ} op a args))
    where aux : {Γ : Ctx} → (op : O) → (a : List (Ctx × T)) → Arg a 𝒫𝒫 Γ → (List (String × ℕ))
          aux op [] args = []
          aux op ((Θ , τ) ∷ []) (pp , n) = ((showBinder n Θ) ++ pp , n + len Θ) ∷ []
          aux op ((Θ , τ) ∷ x ∷ as) ((pp , n) , args) = ((showBinder n Θ) ++ pp , n + len Θ) ∷ aux op (x ∷ as) args

  ppAlg : {τ : T}{Γ : Ctx} → Σ[ op ∈ O ] (τ ≡ Sort op × Arg (Arity op) 𝒫𝒫 Γ) → 𝒫𝒫 τ Γ
  ppAlg {τ} {Γ} (op ⋮ args) =
    let algArgs : 𝒫𝒫 τ Γ
        algArgs = ppAlgArgs {Γ} op (Arity op) args
    in showOp op ++ "(" ++ proj₁ algArgs ++ ")" , proj₂ algArgs

  -- Variables

  varToNat : {τ : T}{Γ : Ctx} → ℐ τ Γ → ℕ
  varToNat new = ℕ.zero
  varToNat (old v) = suc (varToNat v)

  ppVar : {τ : T}{Γ : Ctx} → ℐ τ Γ → 𝒫𝒫 τ Γ
  ppVar v = "x" ++ showNat (varToNat v) , ℕ.zero

  -- Metavariables

  mvarToNat : {τ : T}{Γ : Ctx} → (𝔑 : MCtx) → (Γ ⊩ τ ∈ 𝔑) → ℕ
  mvarToNat 𝔑 ↓ = ℕ.zero
  mvarToNat (⁅ Γ' ⊩ₙ τ' ⁆ 𝔑) (↑ 𝔪) = suc (mvarToNat 𝔑 𝔪)

  ppMvarArgs : {τ : T}{Δ : Ctx} → (Γ : Ctx) → (Γ ~[ 𝒫𝒫 ]↝ Δ) → 𝒫𝒫 τ Δ
  ppMvarArgs {τ}{Δ} Γ ε = join ", " (map proj₁ (aux {τ}{Δ} Γ ε)) , max ℕ.zero (map proj₂ (aux {τ}{Δ} Γ ε))
    where aux : {τ : T}{Δ : Ctx} → (Γ : Ctx) → (Γ ~[ 𝒫𝒫 ]↝ Δ) → (List (String × ℕ))
          aux ∅ ε = []
          aux (α ∙ Γ) ε = (ε {α} new) ∷ (aux {τ}{Δ} Γ (λ v → ε (old v)))

  ppMvar : {τ : T}{Γ : Ctx} → 𝔛 τ Γ → {Δ : Ctx} → (Γ ~[ 𝒫𝒫 ]↝ Δ) → 𝒫𝒫 τ Δ
  ppMvar {τ} {Γ} 𝔪 {Δ} ε rewrite eq {τ}{Γ} =
    let mvarArgs : 𝒫𝒫 τ Δ
        mvarArgs = ppMvarArgs {τ}{Δ} Γ ε
    in "𝔪" ++ showNat (mvarToNat 𝔐 𝔪) ++ "⟨" ++ (proj₁ mvarArgs) ++ "⟩" , proj₂ mvarArgs

  𝒫𝒫ᵃ : MetaAlg ⅀F 𝔛 [_]_ 𝒫𝒫
  𝒫𝒫ᵃ = record {
        𝑎𝑙𝑔 = ppAlg
      ; 𝑣𝑎𝑟 = ppVar
      ; 𝑚𝑣𝑎𝑟 = ppMvar
      ; 𝑏𝑜𝑥 = λ {Ψ} → λ{ (pp , n) → "(box " ++ (showCtx n Ψ) ++ ". " ++ pp ++ ")" , n + len Ψ } }

  open Semantics

  PP : 𝕋 ⇾̣ 𝒫𝒫
  PP = 𝕤𝕖𝕞 𝒫𝒫ᵃ
