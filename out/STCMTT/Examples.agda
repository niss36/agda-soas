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

showT : ΛT → String
showCtx : {A : Set} → (A → A) → (A → String → String) → A → Ctx → String
showCtx next f a ∅ = "∅"
showCtx next f a (α ∙ ∅) = f a (showT α)
showCtx next f a (α ∙ β ∙ Γ) = f a (showT α) ^^ ", " ^^ showCtx next f (next a) (β ∙ Γ)

showT N = "N"
showT (α ↣ β) = showT α ^^ "↣" ^^ showT β
showT ([ Ψ ] τ) = "[" ^^ (showCtx id (λ _ → id) "" Ψ) ^^ "]" ^^ showT τ

showOp : Λₒ → String
showOp appₒ = "app"
showOp lamₒ = "lam"

open import SOAS.FreeVariables {ΛT} [_]_ Λ:Sig 𝕋:Init
open import SOAS.PrettyPrint {ΛT} showT showCtx [_]_ Λ:Sig showOp 𝕋:Init

open import SOAS.ContextMaps.Inductive {ΛT}

module Examples where

  e1 : Λ ⁅⁆ (N ↣ N) ∅
  e1 = ƛ (var new)

  e2 : Λ ⁅⁆ N ((N ↣ N) ∙ N ∙ ∅)
  e2 = (var new) $ var (old new)

  e3 : Λ ⁅⁆ N (N ∙ ∅)
  e3 = (ƛ (var new)) $ (var new)

  e4 : Λ ⁅⁆ (N ↣ (N ↣ N)) ∅
  e4 = ƛ ƛ (var (old new))

  e5 : Λ ⁅⁆ ([ ∅ ] (N ↣ N)) ∅
  e5 = box (∅ , N ↣ N , refl , ƛ var new)

  e6 : Λ ⁅⁆ ([ N ∙ ∅ ] N) ∅
  e6 = box (N ∙ ∅ , N , refl , var new)

  e7 : Λ ⁅⁆ N (([ ∅ ] N) ∙ ∅)
  e7 = letbox (∅ , N , var new , mvar ↓ •)

  e8 : Λ (⁅ ∅ ⊩ₙ [ (N ↣ N) ∙ ∅ ] N ⁆ ⁅⁆) N ∅
  e8 = letbox ( (N ↣ N) ∙ ∅ , N , mvar ↓ • , mvar ↓ ((ƛ var new) ◂ •) )

  e9 : Λ ⁅⁆ N (N ∙ (N ↣ N) ∙ ∅)
  e9 = (ƛ (ƛ var new $ var (old (old new)) ) $ var (old (old new)) ) $ (var (old new) $ var new)

  e10 : Λ ⁅⁆ N ((N ↣ N) ∙ N ∙ ∅)
  e10 = (var new) $ ((ƛ var new) $ var (old new))

  e11 : Λ ⁅⁆ ([ (N ↣ N) ∙ N ∙ ∅ ] N) ∅
  e11 = box ((N ↣ N) ∙ N ∙ ∅ , N , refl , (var new) $ (var (old new)))

  em1 : Λ (⁅ ((N ↣ N) ∙ N ∙ ∅) ⊩ₙ N ⁆ ⁅⁆) N (N ∙ ∅)
  em1 = mvar ↓ ((ƛ var new) ◂ (var new ◂ •))

  em2 : Λ (⁅ N ∙ ∅ ⊩ₙ (N ↣ N) ⁆ ⁅ ((N ↣ N) ∙ N ∙ ∅) ⊩ₙ N ⁆ ⁅⁆) (N ↣ N) ∅
  em2 = ƛ mvar (↑ ↓) (mvar ↓ ((var new) ◂ •) ◂ (var new ◂ •))

  _ : {! PP e11  !}
