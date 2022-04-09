open import Data.Nat
open import Data.Nat.Show renaming (show to showNat)
open import Data.String using (String) renaming (_++_ to _^^_)
open import Data.List using (List; []; _∷_; _++_)

module STCMTT.FreeVariables where

open import STCMTT.Signature
open import STCMTT.Syntax hiding (⅀F)

open import SOAS.Common
open import SOAS.Context {ΛT}
open import SOAS.Variable {ΛT}
open import SOAS.Families.Core {ΛT}

open import SOAS.Metatheory.MetaAlgebra

showT : ℕ → ΛT → String
showCtx : ℕ → Ctx → String

showT _ N = "N"
showT n (α ↣ β) = (showT n α) ^^ "↣" ^^ (showT n β)
showT n ([ Ψ ] τ) = "[" ^^ (showCtx n Ψ) ^^ "]" ^^ (showT n τ)

showCtx n ∅ = "∅"
showCtx n (α ∙ ∅) = "x" ^^ (showNat n) ^^ ": " ^^ (showT (suc n) α)
showCtx n (α ∙ β ∙ Γ) = "x" ^^ (showNat n) ^^ ": " ^^ (showT (suc n) α) ^^ ", " ^^ (showCtx (suc n) (β ∙ Γ))

showOp : Λₒ → String
showOp appₒ = "app"
showOp lamₒ = "lam"

open import SOAS.FreeVariables {ΛT}
open import SOAS.PrettyPrint {ΛT} showCtx

module _ (𝔛 : Familyₛ) where

  -- ℱ𝒱ᵃ : MetaAlg ⅀F 𝔛 [_]_ ℱ𝒱
  -- ℱ𝒱ᵃ = record {
  --     𝑎𝑙𝑔 = λ {τ}{Γ} → λ{ (appₒ ⋮ f , a) → f ++ a ; (lamₒ {α} ⋮ b) → contract¹ {τ}{α}{Γ} b }
  --   ; 𝑣𝑎𝑟 = λ {τ} x → (τ , x) ∷ []
  --   ; 𝑚𝑣𝑎𝑟 = λ {τ}{Γ} 𝔪 {Δ} ε → mvarThing {τ} Γ ε
  --   ; 𝑏𝑜𝑥 = λ x → [] }
  --
  -- FV : Λ 𝔛 ⇾̣ ℱ𝒱
  -- FV = 𝕤𝕖𝕞 𝔛 ℱ𝒱ᵃ
  --
  -- bar : Λ 𝔛 (N ↣ N) (N ∙ ∅)
  -- bar = ƛ (var (old new))
  --
  -- baz : Λ 𝔛 ([ ∅ ] (N ↣ N)) ∅
  -- baz = box ∅ (ƛ var new)
  --
  -- private module FreeVar' = FreeVar 𝔛 [_]_ Λ:Sig (𝕋:Init 𝔛)
  --
  -- f : MetaAlg⇒ {ΛT} ⅀F 𝔛 [_]_ ℱ𝒱ᵃ FreeVar'.ℱ𝒱ᵃ λ z → z
  -- f = record {
  --       ⟨𝑎𝑙𝑔⟩ = λ {α}{Γ} → λ{ {appₒ ⋮ f , a} → refl ; {lamₒ ⋮ b} → refl }
  --     ; ⟨𝑣𝑎𝑟⟩ = refl
  --     ; ⟨𝑚𝑣𝑎𝑟⟩ = refl
  --     ; ⟨𝑏𝑜𝑥⟩ = refl
  --   }
  --
  -- g : MetaAlg⇒ {ΛT} ⅀F 𝔛 [_]_ FreeVar'.ℱ𝒱ᵃ ℱ𝒱ᵃ λ z → z
  -- g = record {
  --       ⟨𝑎𝑙𝑔⟩ = λ {α}{Γ} → λ{ {appₒ ⋮ f , a} → refl ; {lamₒ ⋮ b} → refl }
  --     ; ⟨𝑣𝑎𝑟⟩ = refl
  --     ; ⟨𝑚𝑣𝑎𝑟⟩ = refl
  --     ; ⟨𝑏𝑜𝑥⟩ = refl }

  -- _ : {! MetaAlgebra⇒ {ΛT} ⅀F 𝔛 [_]_ ℱ𝒱ᵃ  !}

  -- h : MetaAlgebra⇒ {ΛT} ⅀F 𝔛 [_]_ ℱ𝒱ᵃ FreeVar'.ℱ𝒱ᵃ
  -- h = ?

open import SOAS.ContextMaps.Inductive {ΛT}

module Examples where

  Thing : Familyₛ → Set
  Thing 𝒜 = (𝔐 : MCtx){τ : ΛT}{Γ : Ctx} → (t : Λ ∥ 𝔐 ∥ τ Γ) → 𝒜 τ Γ

  fv : Thing ℱ𝒱
  fv 𝔐 t = FV t where open FreeVar ∥ 𝔐 ∥ [_]_ Λ:Sig (𝕋:Init ∥ 𝔐 ∥)

  pp : Thing 𝒫𝒫
  pp 𝔐 t = PP t where open PrettyPrint ∥ 𝔐 ∥ {𝔐}{λ {τ}{Γ} → refl} [_]_ Λ:Sig showOp 𝕋:Init

  e1 : {𝒜 : Familyₛ} → Thing 𝒜 → 𝒜 (N ↣ N) ∅
  e1 f = f ⁅⁆ (ƛ (var new))

  e2 : {𝒜 : Familyₛ} → Thing 𝒜 → 𝒜 N ((N ↣ N) ∙ N ∙ ∅)
  e2 f = f ⁅⁆ ((var new) $ var (old new))

  e3 : {𝒜 : Familyₛ} → Thing 𝒜 → 𝒜 N (N ∙ ∅)
  e3 f = f ⁅⁆ ((ƛ (var new)) $ (var new))

  e4 : {𝒜 : Familyₛ} → Thing 𝒜 → 𝒜 (N ↣ (N ↣ N)) ∅
  e4 f = f ⁅⁆ (ƛ ƛ (var (old new)))

  em1 : {𝒜 : Familyₛ} → Thing 𝒜 → 𝒜 N (N ∙ ∅)
  em1 f = f (⁅ ((N ↣ N) ∙ N ∙ ∅) ⊩ₙ N ⁆ ⁅⁆) (mvar ↓ ((ƛ var new) ◂ (var new ◂ •)))

  em2 : {𝒜 : Familyₛ} → Thing 𝒜 → 𝒜 (N ↣ N) ∅
  em2 f = f (⁅ N ∙ ∅ ⊩ₙ (N ↣ N) ⁆ ⁅ ((N ↣ N) ∙ N ∙ ∅) ⊩ₙ N ⁆ ⁅⁆) (ƛ mvar (↑ ↓) (mvar ↓ ((var new) ◂ •) ◂ (var new ◂ •)))

  _ : {! em1 pp  !}
