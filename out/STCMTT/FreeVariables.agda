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

-- open import SOAS.Metatheory.MetaAlgebra

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

-- module _ (𝔛 : Familyₛ) where
--   ℱ𝒱ᵃ : MetaAlg ⅀F 𝔛 [_]_ ℱ𝒱
--   ℱ𝒱ᵃ = record {
--       𝑎𝑙𝑔 = λ {τ}{Γ} → λ{ (appₒ ⋮ f , a) → f ++ a ; (lamₒ {α} ⋮ b) → contract¹ {τ}{α}{Γ} b }
--     ; 𝑣𝑎𝑟 = λ {τ} x → (τ , x) ∷ []
--     ; 𝑚𝑣𝑎𝑟 = λ {τ}{Γ} 𝔪 {Δ} ε → mvarThing {τ} Γ ε
--     ; 𝑏𝑜𝑥 = λ x → [] }
--
--   FV : Λ 𝔛 ⇾̣ ℱ𝒱
--   FV = 𝕤𝕖𝕞 𝔛 ℱ𝒱ᵃ
--
--   bar : Λ 𝔛 (N ↣ N) (N ∙ ∅)
--   bar = ƛ (var (old new))
--
--   baz : Λ 𝔛 ([ ∅ ] (N ↣ N)) ∅
--   baz = box ∅ (ƛ var new)
--
--   private module FreeVar' = FreeVar 𝔛 [_]_ Λ:Sig (𝕋:Init 𝔛)
--
--   f : MetaAlg⇒ {ΛT} ⅀F 𝔛 [_]_ ℱ𝒱ᵃ FreeVar'.ℱ𝒱ᵃ λ z → z
--   f = record {
--         ⟨𝑎𝑙𝑔⟩ = λ {α}{Γ} → λ{ {appₒ ⋮ f , a} → refl ; {lamₒ ⋮ b} → refl }
--       ; ⟨𝑣𝑎𝑟⟩ = refl
--       ; ⟨𝑚𝑣𝑎𝑟⟩ = refl
--       ; ⟨𝑏𝑜𝑥⟩ = refl
--     }
--
--   g : MetaAlg⇒ {ΛT} ⅀F 𝔛 [_]_ FreeVar'.ℱ𝒱ᵃ ℱ𝒱ᵃ λ z → z
--   g = record {
--         ⟨𝑎𝑙𝑔⟩ = λ {α}{Γ} → λ{ {appₒ ⋮ f , a} → refl ; {lamₒ ⋮ b} → refl }
--       ; ⟨𝑣𝑎𝑟⟩ = refl
--       ; ⟨𝑚𝑣𝑎𝑟⟩ = refl
--       ; ⟨𝑏𝑜𝑥⟩ = refl }
--
--   _ : {! MetaAlgebra⇒ {ΛT} ⅀F 𝔛 [_]_ ℱ𝒱ᵃ  !}
--
--   h : MetaAlgebra⇒ {ΛT} ⅀F 𝔛 [_]_ ℱ𝒱ᵃ FreeVar'.ℱ𝒱ᵃ
--   h = ?

open import SOAS.ContextMaps.Inductive {ΛT}

module Examples where
  open FreeVar [_]_ Λ:Sig 𝕋:Init
  open PrettyPrint [_]_ Λ:Sig showOp 𝕋:Init

  e1 : Λ ⁅⁆ (N ↣ N) ∅
  e1 = ƛ (var new)

  e2 : Λ ⁅⁆ N ((N ↣ N) ∙ N ∙ ∅)
  e2 = (var new) $ var (old new)

  e3 : Λ ⁅⁆ N (N ∙ ∅)
  e3 = (ƛ (var new)) $ (var new)

  e4 : Λ ⁅⁆ (N ↣ (N ↣ N)) ∅
  e4 = ƛ ƛ (var (old new))

  e5 : Λ ⁅⁆ ([ ∅ ] (N ↣ N)) ∅
  e5 = box ∅ (ƛ var new)

  e6 : Λ ⁅⁆ ([ N ∙ ∅ ] N) ∅
  e6 = box (N ∙ ∅) (var new)

  em1 : Λ (⁅ ((N ↣ N) ∙ N ∙ ∅) ⊩ₙ N ⁆ ⁅⁆) N (N ∙ ∅)
  em1 = mvar ↓ ((ƛ var new) ◂ (var new ◂ •))

  em2 : Λ (⁅ N ∙ ∅ ⊩ₙ (N ↣ N) ⁆ ⁅ ((N ↣ N) ∙ N ∙ ∅) ⊩ₙ N ⁆ ⁅⁆) (N ↣ N) ∅
  em2 = ƛ mvar (↑ ↓) (mvar ↓ ((var new) ◂ •) ◂ (var new ◂ •))

  _ : {! PP e6  !}
