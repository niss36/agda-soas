
open import SOAS.Context
open import SOAS.Metatheory.Syntax

-- Metatheory of a second-order syntax
module SOAS.Metatheory {T : Set}
  ([_]_ : Ctx {T} → T → T)
  (Syn : Syntax {T} [_]_) where

open import SOAS.Families.Core {T}

open import SOAS.Abstract.ExpStrength

open Syntax Syn

open CompatStrengths ⅀:CS public renaming (CoalgStr to ⅀:Str ; ExpStr to ⅀:ExpStr)

open import SOAS.Metatheory.Algebra ⅀F public
open import SOAS.Metatheory.Monoid ⅀F ⅀:Str public

module Theory where
  open import SOAS.Metatheory.MetaAlgebra   [_]_ ⅀F public
  open import SOAS.Metatheory.Semantics     [_]_ ⅀F ⅀:Str 𝕋:Init public
  open import SOAS.Metatheory.Traversal     [_]_ ⅀F ⅀:Str 𝕋:Init public
  open import SOAS.Metatheory.Renaming      [_]_ ⅀F ⅀:Str 𝕋:Init public
  open import SOAS.Metatheory.Coalgebraic   [_]_ ⅀F ⅀:Str 𝕋:Init public
  open import SOAS.Metatheory.Substitution  [_]_ ⅀F ⅀:Str 𝕋:Init public
