open import Data.Nat
open import Data.Nat.Show renaming (show to showNat)
open import Data.String using (String) renaming (_++_ to _^^_)
open import Data.List using (List; []; _∷_; _++_)

module STCMTT.Examples where

open import STCMTT.Signature
open import STCMTT.Syntax hiding (⅀F)

open import SOAS.Common
open import SOAS.Context {ΛT}
open import SOAS.Variable {ΛT}
open import SOAS.Families.Core {ΛT}

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
open import SOAS.PrettyPrint {ΛT} showT showCtx

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

  e7 : Λ ⁅⁆ N (([ ∅ ] N) ∙ ∅)
  e7 = letbox (∅ , N , var new , mvar ↓ •)

  e8 : Λ (⁅ ∅ ⊩ₙ [ (N ↣ N) ∙ ∅ ] N ⁆ ⁅⁆) N ∅
  e8 = letbox ( (N ↣ N) ∙ ∅ , N , mvar ↓ • , mvar ↓ ((ƛ var new) ◂ •) )

  em1 : Λ (⁅ ((N ↣ N) ∙ N ∙ ∅) ⊩ₙ N ⁆ ⁅⁆) N (N ∙ ∅)
  em1 = mvar ↓ ((ƛ var new) ◂ (var new ◂ •))

  em2 : Λ (⁅ N ∙ ∅ ⊩ₙ (N ↣ N) ⁆ ⁅ ((N ↣ N) ∙ N ∙ ∅) ⊩ₙ N ⁆ ⁅⁆) (N ↣ N) ∅
  em2 = ƛ mvar (↑ ↓) (mvar ↓ ((var new) ◂ •) ◂ (var new ◂ •))

  _ : {! PP e8  !}
