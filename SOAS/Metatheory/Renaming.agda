
open import SOAS.Common
open import SOAS.Families.Core
open import Categories.Object.Initial
open import SOAS.Coalgebraic.Strength
import SOAS.Metatheory.MetaAlgebra
import SOAS.Context

-- Renaming structure by initiality
module SOAS.Metatheory.Renaming {T : Set}
  (open SOAS.Context {T})
  ([_]_ : Ctx → T → T)
  (⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ) (⅀:Str : Strength ⅀F)
  (open SOAS.Metatheory.MetaAlgebra [_]_ ⅀F)
  (𝕋:Init : Initial 𝕄etaAlgebras)
  where

open import SOAS.Variable
open import SOAS.Abstract.Hom
import SOAS.Abstract.Coalgebra as →□ ; open →□.Sorted
import SOAS.Abstract.Box as □ ; open □.Sorted

open import SOAS.Coalgebraic.Map

open import SOAS.Metatheory.Algebra {T} ⅀F
open import SOAS.Metatheory.Semantics [_]_ ⅀F ⅀:Str 𝕋:Init
open import SOAS.Metatheory.Traversal [_]_ ⅀F ⅀:Str 𝕋:Init

open Strength ⅀:Str

-- Renaming is a ℐ-parametrised traversal into 𝕋
module Renaming = □Traversal 𝕋ᵃ

𝕣𝕖𝕟 : 𝕋 ⇾̣₂ (□ ²) 𝕋
𝕣𝕖𝕟 = Renaming.𝕥𝕣𝕒𝕧

𝕨𝕜 : {𝔐 : MCtx}{α τ : T}{Γ : Ctx} → 𝕋 𝔐 α Γ → 𝕋 𝔐 α (τ ∙ Γ)
𝕨𝕜 t = 𝕣𝕖𝕟 t old

-- Comultiplication law
𝕣𝕖𝕟-comp : MapEq₂ ℐᴮ ℐᴮ 𝕒𝕝𝕘 𝕓𝕠𝕩
                  (λ t ρ ϱ → 𝕣𝕖𝕟 t (ϱ ∘ ρ))
                  (λ t ρ ϱ → 𝕣𝕖𝕟 (𝕣𝕖𝕟 t ρ) ϱ)
𝕣𝕖𝕟-comp = record
  { φ = 𝕧𝕒𝕣
  ; ϕ = λ x ρ → 𝕧𝕒𝕣 (ρ x)
  ; χ = 𝕞𝕧𝕒𝕣
  ; f⟨𝑣⟩ = 𝕥⟨𝕧⟩
  ; f⟨𝑚⟩ = 𝕥⟨𝕞⟩
  ; f⟨𝑎⟩ = λ{ {𝔐 = 𝔐}{σ = ρ}{ϱ}{t} → begin
        𝕣𝕖𝕟 (𝕒𝕝𝕘 t) (ϱ ∘ ρ)
    ≡⟨ 𝕥⟨𝕒⟩ ⟩
        𝕒𝕝𝕘 (str ℐᴮ (𝕋 𝔐) (⅀₁ 𝕣𝕖𝕟 t) (ϱ ∘ ρ))
    ≡⟨ cong 𝕒𝕝𝕘 (str-dist (𝕋 𝔐) (jᶜ ℐᴮ) (⅀₁ 𝕣𝕖𝕟 t) ρ ϱ) ⟩
    𝕒𝕝𝕘 (str ℐᴮ (𝕋 𝔐) (str ℐᴮ (□ (𝕋 𝔐)) (⅀₁ (precomp (𝕋 𝔐) (j ℐ)) (⅀₁ 𝕣𝕖𝕟 t)) ρ) ϱ)
    ≡˘⟨ congr ⅀.homomorphism (λ - → 𝕒𝕝𝕘 (str ℐᴮ (𝕋 𝔐) (str ℐᴮ (□ (𝕋 𝔐)) - ρ) ϱ)) ⟩
        𝕒𝕝𝕘 (str ℐᴮ (𝕋 𝔐) (str ℐᴮ (□ (𝕋 𝔐)) (⅀₁ (λ{ t ρ ϱ → 𝕣𝕖𝕟 t (ϱ ∘ ρ)}) t) ρ) ϱ)
    ∎ }
  ; f⟨𝑏⟩ = 𝕥⟨𝕓⟩
  ; g⟨𝑣⟩ = trans (𝕥≈₁ 𝕥⟨𝕧⟩) 𝕥⟨𝕧⟩
  ; g⟨𝑚⟩ = trans (𝕥≈₁ 𝕥⟨𝕞⟩) 𝕥⟨𝕞⟩
  ; g⟨𝑎⟩ = λ{ {𝔐 = 𝔐}{σ = ρ}{ϱ}{t} → begin
        𝕣𝕖𝕟 (𝕣𝕖𝕟 (𝕒𝕝𝕘 t) ρ) ϱ
    ≡⟨ 𝕥≈₁ 𝕥⟨𝕒⟩ ⟩
        𝕣𝕖𝕟 (𝕒𝕝𝕘 (str ℐᴮ (𝕋 𝔐) (⅀₁ 𝕣𝕖𝕟 t) ρ)) ϱ
    ≡⟨ 𝕥⟨𝕒⟩ ⟩
        𝕒𝕝𝕘 (str ℐᴮ (𝕋 𝔐) (⅀₁ 𝕣𝕖𝕟 (str ℐᴮ (𝕋 𝔐) (⅀₁ 𝕣𝕖𝕟 t) ρ)) ϱ)
    ≡˘⟨ congr (str-nat₂ 𝕣𝕖𝕟 (⅀₁ 𝕣𝕖𝕟 t) ρ) (λ - → 𝕒𝕝𝕘 (str ℐᴮ (𝕋 𝔐) - ϱ)) ⟩
        𝕒𝕝𝕘 (str ℐᴮ (𝕋 𝔐) (str ℐᴮ (□ (𝕋 𝔐)) (⅀.F₁ (λ { h′ ς → 𝕣𝕖𝕟 (h′ ς) }) (⅀₁ 𝕣𝕖𝕟 t)) ρ) ϱ)
    ≡˘⟨ congr ⅀.homomorphism (λ - → 𝕒𝕝𝕘 (str ℐᴮ (𝕋 𝔐) (str ℐᴮ (□ (𝕋 𝔐)) - ρ) ϱ)) ⟩
        𝕒𝕝𝕘 (str ℐᴮ (𝕋 𝔐) (str ℐᴮ (□ (𝕋 𝔐)) (⅀₁ (λ{ t ρ ϱ → 𝕣𝕖𝕟 (𝕣𝕖𝕟 t ρ) ϱ}) t) ρ) ϱ)
    ∎ }
  ; g⟨𝑏⟩ = trans (𝕥≈₁ 𝕥⟨𝕓⟩) 𝕥⟨𝕓⟩
  }
  where
  open ≡-Reasoning
  open Renaming


-- Pointed □-coalgebra structure for 𝕋
𝕋ᵇ : {𝔐 : MCtx} → Coalg (𝕋 𝔐)
𝕋ᵇ = record { r = 𝕣𝕖𝕟 ; counit = □𝕥𝕣𝕒𝕧-id≈id
            ; comult = λ{ {t = t} → MapEq₂.≈ 𝕣𝕖𝕟-comp t } }

𝕋ᴮ : {𝔐 : MCtx} → Coalgₚ (𝕋 𝔐)
𝕋ᴮ = record { ᵇ = 𝕋ᵇ ; η = 𝕧𝕒𝕣 ; r∘η = Renaming.𝕥⟨𝕧⟩ }
