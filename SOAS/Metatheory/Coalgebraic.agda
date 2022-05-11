
open import SOAS.Common
open import SOAS.Families.Core
open import Categories.Object.Initial
open import SOAS.Coalgebraic.Strength
import SOAS.Metatheory.MetaAlgebra
import SOAS.Context

-- Coalgebraic traversal maps
module SOAS.Metatheory.Coalgebraic {T : Set}
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
open import SOAS.Metatheory.Contextual [_]_
open import SOAS.Metatheory.Semantics [_]_ ⅀F ⅀:Str 𝕋:Init
open import SOAS.Metatheory.Traversal [_]_ ⅀F ⅀:Str 𝕋:Init
open import SOAS.Metatheory.Renaming [_]_ ⅀F ⅀:Str 𝕋:Init

open Strength ⅀:Str

-- Relationship of traversal and interpretation, assuming 𝓐 has compatible renaming structure
module _ {𝓐 : Family₂}(𝓐ᵇ : {𝔐 : MCtx} → Coalg (𝓐 𝔐))(𝓐ᵃ : MetaAlg 𝓐)
         (open Semantics 𝓐ᵃ)
         (rᵃ⇒ : MetaAlg⇒ 𝓐ᵃ (□ᵃ 𝓐ᵃ) (Coalg.r 𝓐ᵇ)) where

  private
    open module - {𝔐} = Coalg (𝓐ᵇ {𝔐})

  open MetaAlg 𝓐ᵃ
  open MetaAlg⇒ rᵃ⇒

  𝓐ᴮ : {𝔐 : MCtx} → Coalgₚ (𝓐 𝔐)
  𝓐ᴮ = record { ᵇ = 𝓐ᵇ ; η = 𝑣𝑎𝑟 ; r∘η = cong (λ - → - _) ⟨𝑣𝑎𝑟⟩ }

  -- Interpretation and renaming commute
  𝕤𝕖𝕞∘ren : MapEq₁ ℐᴮ 𝑎𝑙𝑔 𝑏𝑜𝑥 (λ t ρ → 𝕤𝕖𝕞 (𝕣𝕖𝕟 t ρ)) (λ t ρ → r (𝕤𝕖𝕞 t) ρ)
  𝕤𝕖𝕞∘ren = record
    { φ = 𝑣𝑎𝑟
    ; χ = 𝑚𝑣𝑎𝑟
    ; f⟨𝑣⟩ = trans (cong 𝕤𝕖𝕞 Renaming.𝕥⟨𝕧⟩) ⟨𝕧⟩
    ; f⟨𝑚⟩ = trans (cong 𝕤𝕖𝕞 Renaming.𝕥⟨𝕞⟩) ⟨𝕞⟩
    ; f⟨𝑎⟩ = λ{ {𝔐 = 𝔐}{σ = σ}{t} → begin
          𝕤𝕖𝕞 (𝕣𝕖𝕟 (𝕒𝕝𝕘 t) σ)
      ≡⟨ cong 𝕤𝕖𝕞 Renaming.𝕥⟨𝕒⟩ ⟩
          𝕤𝕖𝕞 (𝕒𝕝𝕘 (str ℐᴮ (𝕋 𝔐) (⅀₁ 𝕣𝕖𝕟 t) σ))
      ≡⟨ ⟨𝕒⟩ ⟩
          𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 (str ℐᴮ (𝕋 𝔐) (⅀₁ 𝕣𝕖𝕟 t) σ))
      ≡˘⟨ cong 𝑎𝑙𝑔 (str-nat₂ 𝕤𝕖𝕞 (⅀₁ 𝕣𝕖𝕟 t) σ) ⟩
          𝑎𝑙𝑔 (str ℐᴮ (𝓐 𝔐) (⅀.F₁ (λ { h′ ς → 𝕤𝕖𝕞 (h′ ς) }) (⅀₁ 𝕣𝕖𝕟 t)) σ)
      ≡˘⟨ congr ⅀.homomorphism (λ - → 𝑎𝑙𝑔 (str ℐᴮ (𝓐 𝔐) - σ)) ⟩
          𝑎𝑙𝑔 (str ℐᴮ (𝓐 𝔐) (⅀₁ (λ{ t ρ → 𝕤𝕖𝕞 (𝕣𝕖𝕟 t ρ)}) t) σ)
      ∎ }
    ; f⟨𝑏⟩ = trans (cong 𝕤𝕖𝕞 Renaming.𝕥⟨𝕓⟩) ⟨𝕓⟩
    ; g⟨𝑣⟩ = trans (r≈₁ ⟨𝕧⟩) (cong (λ - → - _) ⟨𝑣𝑎𝑟⟩)
    ; g⟨𝑚⟩ = trans (r≈₁ ⟨𝕞⟩) (cong (λ - → - _) ⟨𝑚𝑣𝑎𝑟⟩)
    ; g⟨𝑎⟩ = λ{ {𝔐 = 𝔐}{σ = σ}{t} → begin
          r (𝕤𝕖𝕞 (𝕒𝕝𝕘 t)) σ
      ≡⟨ r≈₁ ⟨𝕒⟩ ⟩
          r (𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)) σ
      ≡⟨ cong (λ - → - σ) ⟨𝑎𝑙𝑔⟩ ⟩
          𝑎𝑙𝑔 (str ℐᴮ (𝓐 𝔐) (⅀₁ r (⅀₁ 𝕤𝕖𝕞 t)) σ)
      ≡˘⟨ congr ⅀.homomorphism (λ - → 𝑎𝑙𝑔 (str ℐᴮ (𝓐 𝔐) - σ)) ⟩
          𝑎𝑙𝑔 (str ℐᴮ (𝓐 𝔐) (⅀₁ (λ{ t ρ → r (𝕤𝕖𝕞 t) ρ}) t) σ)
      ∎ }
    ; g⟨𝑏⟩ = trans (r≈₁ ⟨𝕓⟩) (cong (λ - → - _) ⟨𝑏𝑜𝑥⟩)
    } where open ≡-Reasoning

  -- Interpretation is a pointed □-coalgebra homomorphism
  𝕤𝕖𝕞ᵇ⇒ : {𝔐 : MCtx} → Coalg⇒ 𝕋ᵇ (𝓐ᵇ {𝔐}) 𝕤𝕖𝕞
  𝕤𝕖𝕞ᵇ⇒ = record { ⟨r⟩ = λ{ {t = t} → MapEq₁.≈ 𝕤𝕖𝕞∘ren t } }

  𝕤𝕖𝕞ᴮ⇒ : {𝔐 : MCtx} → Coalgₚ⇒ 𝕋ᴮ (𝓐ᴮ {𝔐}) 𝕤𝕖𝕞
  𝕤𝕖𝕞ᴮ⇒ = record { ᵇ⇒ = 𝕤𝕖𝕞ᵇ⇒ ; ⟨η⟩ = ⟨𝕧⟩ }

-- Coalgebraic traversal maps
module Travᶜ {𝓟 𝓐 : Family₂}(𝓟ᴮ : {𝔐 : MCtx} → Coalgₚ (𝓟 𝔐))
             (𝑎𝑙𝑔 : (⅀ ²) 𝓐 ⇾̣₂ 𝓐)
             (φ : 𝓟 ⇾̣₂ 𝓐)
             (χ : ∥_∥ ⇾̣₂ 〖 𝓐 , 𝓐 〗²)
             (𝑏𝑜𝑥 : (B ²) 𝓐 ⇾̣₂ 𝓐) where

  private
    open module - {𝔐} = Coalgₚ (𝓟ᴮ {𝔐})

  open Traversal 𝓟ᴮ 𝑎𝑙𝑔 φ χ 𝑏𝑜𝑥

  -- Traversal is derived from 𝕤𝕖𝕞, so it is also a pointed coalgebra homomorphism
  𝕥𝕣𝕒𝕧ᵇ⇒ : {𝔐 : MCtx} → Coalg⇒ 𝕋ᵇ (Travᵇ {𝔐}) 𝕥𝕣𝕒𝕧
  𝕥𝕣𝕒𝕧ᵇ⇒ = 𝕤𝕖𝕞ᵇ⇒ Travᵇ Travᵃ record
    { ⟨𝑎𝑙𝑔⟩ = λ{ {𝔐}{t = t} → dext² (λ ρ ς → cong 𝑎𝑙𝑔 (str-dist (𝓐 𝔐) (jᶜ 𝓟ᴮ) t ρ ς)) }
    ; ⟨𝑣𝑎𝑟⟩ = refl ; ⟨𝑚𝑣𝑎𝑟⟩ = refl; ⟨𝑏𝑜𝑥⟩ = refl }

  𝕥𝕣𝕒𝕧ᴮ⇒ : {𝔐 : MCtx} → Coalgₚ⇒ 𝕋ᴮ (Travᴮ {𝔐}) 𝕥𝕣𝕒𝕧
  𝕥𝕣𝕒𝕧ᴮ⇒  = record { ᵇ⇒ = 𝕥𝕣𝕒𝕧ᵇ⇒ ; ⟨η⟩ = ⟨𝕧⟩ }

  -- Assuming 𝓐 is also a pointed □-coalgebra, traversal also commutes with renaming
  module _ (𝓐ᴮ : {𝔐 : MCtx} → Coalgₚ (𝓐 𝔐))(φᴮ : {𝔐 : MCtx} → Coalgₚ⇒ (𝓟ᴮ {𝔐}) (𝓐ᴮ {𝔐}) φ)
           (𝓐rᵃ : MetaAlg⇒ 𝓐ᵃ (□ᵃ 𝓐ᵃ) (Coalgₚ.r 𝓐ᴮ)) where

    private module 𝓐ᴮ {𝔐} = Coalgₚ (𝓐ᴮ {𝔐})
    private module φᴮ {𝔐} = Coalgₚ⇒ (φᴮ {𝔐})
    private module 𝓐rᵃ = MetaAlg⇒ 𝓐rᵃ

    -- Renaming and interpretation can commute
    r∘𝕥𝕣𝕒𝕧 : MapEq₂ 𝓟ᴮ ℐᴮ 𝑎𝑙𝑔 𝑏𝑜𝑥 (λ t σ ϱ → 𝓐ᴮ.r (𝕥𝕣𝕒𝕧 t σ) ϱ) (λ t σ ϱ → 𝕥𝕣𝕒𝕧 t (λ v → r (σ v) ϱ))
    r∘𝕥𝕣𝕒𝕧 = record
      { φ = 𝓐ᴮ.η
      ; ϕ = λ v → 𝓐ᴮ.r (φ v)
      ; χ = χ
      ; f⟨𝑣⟩ = 𝓐ᴮ.r≈₁ 𝕥⟨𝕧⟩
      ; f⟨𝑚⟩ = trans (𝓐ᴮ.r≈₁ 𝕥⟨𝕞⟩) (cong (λ - → - _) 𝓐rᵃ.⟨𝑚𝑣𝑎𝑟⟩)
      ; f⟨𝑎⟩ = λ{ {𝔐 = 𝔐}{σ = σ}{ϱ}{t} → begin
            𝓐ᴮ.r (𝕥𝕣𝕒𝕧 (𝕒𝕝𝕘 t) σ) ϱ
        ≡⟨ 𝓐ᴮ.r≈₁ 𝕥⟨𝕒⟩ ⟩
            𝓐ᴮ.r (𝑎𝑙𝑔 (str 𝓟ᴮ (𝓐 𝔐) (⅀₁ 𝕥𝕣𝕒𝕧 t) σ)) ϱ
        ≡⟨ cong (λ - → - ϱ) 𝓐rᵃ.⟨𝑎𝑙𝑔⟩ ⟩
            𝑎𝑙𝑔 (str ℐᴮ (𝓐 𝔐) (⅀.F₁ 𝓐ᴮ.r (str 𝓟ᴮ (𝓐 𝔐) (⅀.F₁ 𝕥𝕣𝕒𝕧 t) σ)) ϱ)
        ≡˘⟨ congr (str-nat₂ 𝓐ᴮ.r (⅀.F₁ 𝕥𝕣𝕒𝕧 t) σ) (λ - → 𝑎𝑙𝑔 (str ℐᴮ (𝓐 𝔐) - ϱ)) ⟩
            𝑎𝑙𝑔 (str ℐᴮ (𝓐 𝔐) (str 𝓟ᴮ (□ (𝓐 𝔐)) (⅀.F₁ (λ { h ς → 𝓐ᴮ.r (h ς) }) (⅀.F₁ 𝕥𝕣𝕒𝕧 t)) σ) ϱ)
        ≡˘⟨ congr ⅀.homomorphism (λ - → 𝑎𝑙𝑔 (str ℐᴮ (𝓐 𝔐) (str 𝓟ᴮ (□ (𝓐 𝔐)) - σ)  ϱ)) ⟩
            𝑎𝑙𝑔 (str ℐᴮ (𝓐 𝔐) (str 𝓟ᴮ (□ (𝓐 𝔐)) (⅀₁ (λ{ t σ → 𝓐ᴮ.r (𝕥𝕣𝕒𝕧 t σ)}) t) σ)  ϱ)
        ∎ }
      ; f⟨𝑏⟩ = trans (𝓐ᴮ.r≈₁ 𝕥⟨𝕓⟩) (cong (λ - → - _) 𝓐rᵃ.⟨𝑏𝑜𝑥⟩)
      ; g⟨𝑣⟩ = trans 𝕥⟨𝕧⟩ φᴮ.⟨r⟩
      ; g⟨𝑚⟩ = 𝕥⟨𝕞⟩
      ; g⟨𝑎⟩ = λ{ {𝔐 = 𝔐}{σ = σ}{ϱ}{t} → begin
            𝕥𝕣𝕒𝕧 (𝕒𝕝𝕘 t) (λ x → r (σ x) ϱ)
        ≡⟨ 𝕥⟨𝕒⟩ ⟩
            𝑎𝑙𝑔 (str 𝓟ᴮ (𝓐 𝔐) (⅀₁ 𝕥𝕣𝕒𝕧 t) (λ x → r (σ x) ϱ))
        ≡⟨ cong 𝑎𝑙𝑔 (str-dist (𝓐 𝔐) (rᶜ 𝓟ᴮ) (⅀₁ 𝕥𝕣𝕒𝕧 t) σ ϱ) ⟩
            𝑎𝑙𝑔 (str ℐᴮ (𝓐 𝔐) (str 𝓟ᴮ (□ (𝓐 𝔐)) (⅀.F₁ (precomp (𝓐 𝔐) r) (⅀₁ 𝕥𝕣𝕒𝕧 t)) σ) ϱ)
        ≡˘⟨ congr ⅀.homomorphism (λ - → 𝑎𝑙𝑔 (str ℐᴮ (𝓐 𝔐) (str 𝓟ᴮ (□ (𝓐 𝔐)) - σ) ϱ)) ⟩
            𝑎𝑙𝑔 (str ℐᴮ (𝓐 𝔐)  (str 𝓟ᴮ (□ (𝓐 𝔐)) (⅀₁ (λ{ t σ ϱ → 𝕥𝕣𝕒𝕧 t (λ v → r (σ v) ϱ)}) t) σ) ϱ)
        ∎ }
      ; g⟨𝑏⟩ = λ{ {Γ = Γ}{α = α}{𝔐 = 𝔐}{σ = σ}{ϱ}{b} → trans 𝕥⟨𝕓⟩ (cong 𝑏𝑜𝑥 (BF:Str.str-dist (𝓐 𝔐) (rᶜ 𝓟ᴮ) (B₁ 𝕥𝕣𝕒𝕧 {α}{Γ} b) σ ϱ)) }
      } where open ≡-Reasoning

    -- The traversal map 𝕋 ⇾ 〖𝓟, 𝓐〗 is pointed coalgebraic if 𝓐 has coalgebra structure
    𝕥𝕣𝕒𝕧ᶜ : {𝔐 : MCtx} → Coalgebraic 𝕋ᴮ (𝓟ᴮ {𝔐}) (𝓐ᴮ {𝔐}) 𝕥𝕣𝕒𝕧
    𝕥𝕣𝕒𝕧ᶜ = record { r∘f = λ{ {σ = σ}{ϱ}{t = t} → MapEq₂.≈ r∘𝕥𝕣𝕒𝕧 t }
                  ; f∘r = λ{ {ρ = ρ}{ς}{t = t} → cong (λ - → - ς) (Coalg⇒.⟨r⟩ 𝕥𝕣𝕒𝕧ᵇ⇒ {ρ = ρ}{t = t}) }
                  ; f∘η = trans 𝕥⟨𝕧⟩ φᴮ.⟨η⟩ }
