open import SOAS.Common

open import Data.Nat
open import Data.Nat.Show renaming (show to showNat)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Extrema.Nat
open import Data.String using (String; _++_) renaming (intersperse to join)

import SOAS.Context

module SOAS.PrettyPrint {T : Set}
  (open SOAS.Context {T})
  (showT : ℕ → T → String)
  (showCtx : ℕ → Ctx → String) where

open import SOAS.Variable
open import SOAS.Families.Core {T}

𝓟𝓟 : Family₂
𝓟𝓟 𝔐 τ Γ = String × ℕ × ℕ

len : Ctx → ℕ
len ∅ = ℕ.zero
len (α ∙ Γ) = suc (len Γ)

unzip : {A B : Set} → List (A × B) → (List A) × (List B)
unzip l = (map proj₁ l) , (map proj₂ l)

unzip³ : {A B C : Set} → List (A × B × C) → (List A) × (List B) × (List C)
unzip³ l = let z = unzip l in (proj₁ z) , (unzip (proj₂ z))

open import Categories.Object.Initial

open import SOAS.Syntax.Arguments {T}
open import SOAS.Syntax.Signature T

open import SOAS.Metatheory.MetaAlgebra {T}

module PrettyPrint
  ([_]_ : Ctx → T → T)
  {O : Set}(𝕋:Sig : Signature O)
  (showOp : O → String)
  (open Signature 𝕋:Sig)
  (𝕋:Init : Initial (𝕄etaAlgebras [_]_ ⅀F)) where

  open import SOAS.Abstract.ExpStrength
  open CompatStrengths ⅀:CompatStr
  open import SOAS.Metatheory.Semantics {T} [_]_ ⅀F CoalgStr 𝕋:Init

  -- Operators

  showBinder : ℕ → Ctx → String
  showBinder n ∅ = ""
  showBinder n (α ∙ Γ) = (showCtx n (α ∙ Γ)) ++ ". "

  ppAlgArgs : {𝔐 : MCtx}{Γ : Ctx} → (op : O) → (a : List (Ctx × T)) → Arg a (𝓟𝓟 𝔐) Γ → 𝓟𝓟 𝔐 (Sort op) Γ
  ppAlgArgs {𝔐}{Γ} op a args = aux (unzip³ (rec a args))
    where rec : (a : List (Ctx × T)) → Arg a (𝓟𝓟 𝔐) Γ → (List (String × ℕ × ℕ))
          rec [] args = []
          rec ((Θ , τ) ∷ []) (pp , m , n) = ((showBinder n Θ) ++ pp , m , n + len Θ) ∷ []
          rec ((Θ , τ) ∷ x ∷ as) ((pp , m , n) , args) = ((showBinder n Θ) ++ pp , m , n + len Θ) ∷ rec (x ∷ as) args

          aux : List String × List ℕ × List ℕ → 𝓟𝓟 𝔐 (Sort op) Γ
          aux (ss , ms , ns) = join ", " ss , max ℕ.zero ms , max ℕ.zero ns

  ppAlg : {𝔐 : MCtx}{τ : T}{Γ : Ctx} → Σ[ op ∈ O ] (τ ≡ Sort op × Arg (Arity op) (𝓟𝓟 𝔐) Γ) → 𝓟𝓟 𝔐 τ Γ
  ppAlg {𝔐}{τ}{Γ} (op ⋮ args) =
    let algArgs = ppAlgArgs {𝔐}{Γ} op (Arity op) args
    in showOp op ++ "(" ++ proj₁ algArgs ++ ")" , proj₂ algArgs

  -- Variables

  varToNat : {τ : T}{Γ : Ctx} → ℐ τ Γ → ℕ
  varToNat new = ℕ.zero
  varToNat (old v) = suc (varToNat v)

  ppVar : {𝔐 : MCtx}{τ : T}{Γ : Ctx} → ℐ τ Γ → 𝓟𝓟 𝔐 τ Γ
  ppVar v = "x" ++ showNat (varToNat v) , ℕ.zero , ℕ.zero

  -- Metavariables

  mvarToNat : (𝔐 : MCtx) → {τ : T}{Γ : Ctx} → (Γ ⊩ τ ∈ 𝔐) → ℕ
  mvarToNat 𝔐 ↓ = ℕ.zero
  mvarToNat (⁅ Γ' ⊩ₙ τ' ⁆ 𝔐) (↑ 𝔪) = suc (mvarToNat 𝔐 𝔪)

  ppMvarArgs : {𝔐 : MCtx}{τ : T}{Δ : Ctx} → (Γ : Ctx) → (Γ ~[ 𝓟𝓟 𝔐 ]↝ Δ) → 𝓟𝓟 𝔐 τ Δ
  ppMvarArgs {𝔐}{τ}{Δ} Γ ε = aux (unzip³ (rec Γ ε))
    where rec : (Γ : Ctx) → (Γ ~[ 𝓟𝓟 𝔐 ]↝ Δ) → (List (String × ℕ × ℕ))
          rec ∅ ε = []
          rec (α ∙ Γ) ε = (ε {α} new) ∷ (rec Γ (λ v → ε (old v)))

          aux : List String × List ℕ × List ℕ → 𝓟𝓟 𝔐 τ Δ
          aux (ss , ms , ns) = join ", " ss , max ℕ.zero ms , max ℕ.zero ns

  ppMvar : {𝔐 : MCtx}{τ : T}{Γ : Ctx} → (Γ ⊩ τ ∈ 𝔐) → {Δ : Ctx} → (Γ ~[ 𝓟𝓟 𝔐 ]↝ Δ) → 𝓟𝓟 𝔐 τ Δ
  ppMvar {𝔐}{τ}{Γ} 𝔪 {Δ} ε =
    let mvarArgs = ppMvarArgs {𝔐}{τ}{Δ} Γ ε
    in "𝔪" ++ showNat (mvarToNat 𝔐 𝔪) ++ "⟨" ++ (proj₁ mvarArgs) ++ "⟩" , proj₂ mvarArgs

  𝓟𝓟ᵃ : MetaAlg [_]_ ⅀F 𝓟𝓟
  𝓟𝓟ᵃ = record {
        𝑎𝑙𝑔 = λ {𝔐} → ppAlg {𝔐}
      ; 𝑣𝑎𝑟 = λ {𝔐} → ppVar {𝔐}
      ; 𝑚𝑣𝑎𝑟 = λ {𝔐} → ppMvar {𝔐}
      ; 𝑏𝑜𝑥 = λ {Ψ} → λ{ (pp , m , n) → "box(" ++ (showCtx n Ψ) ++ ". " ++ pp ++ ")" , m , n + len Ψ }
      ; 𝑙𝑒𝑡𝑏𝑜𝑥 = λ { (Ψ , α , (fst , fm , fn) , (snd , sm , sn)) → "letbox(" ++ fst ++ ", " ++ "𝔪" ++ (showNat sm) ++ ": " ++ (showCtx sn Ψ) ++ "⊩" ++ (showT sn α) ++ ". " ++ snd ++ ")" , fm Data.Nat.⊔ (suc sm) , fn Data.Nat.⊔ sn } }

  open Semantics

  PP : 𝕋 ⇾̣₂ 𝓟𝓟
  PP = 𝕤𝕖𝕞 𝓟𝓟ᵃ
