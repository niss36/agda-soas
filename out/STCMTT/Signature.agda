module STCMTT.Signature where

open import SOAS.Context

-- Type declaration
data ΛT : Set where
  N   : ΛT
  _↣_ : ΛT → ΛT → ΛT
  [_]_ : Ctx {ΛT} → ΛT → ΛT
infixr 30 _↣_
infixr 20 [_]_


open import SOAS.Syntax.Signature ΛT public
open import SOAS.Syntax.Build ΛT public

-- Operator symbols
data Λₒ : Set where
  appₒ lamₒ : {α β : ΛT} → Λₒ

-- Term signature
Λ:Sig : Signature Λₒ
Λ:Sig = sig λ
  { (appₒ {α}{β}) → (⊢₀ α ↣ β) , (⊢₀ α) ⟼₂ β
  ; (lamₒ {α}{β}) → (α ⊢₁ β) ⟼₁ α ↣ β
  }

open Signature Λ:Sig public
