
open import SOAS.Common
open import SOAS.Families.Core
open import Categories.Object.Initial
open import SOAS.Coalgebraic.Strength
import SOAS.Metatheory.MetaAlgebra
import SOAS.Context

-- Initial-algebra semantics
module SOAS.Metatheory.Semantics {T : Set}
  (open SOAS.Context {T})
  ([_]_ : Ctx → T → T)
  (⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ) (⅀:Str : Strength ⅀F)
  (open SOAS.Metatheory.MetaAlgebra [_]_ ⅀F)
  (𝕋:Init : Initial 𝕄etaAlgebras)
  where

open import SOAS.Variable
open import SOAS.Construction.Structure as Structure
open import SOAS.Abstract.Hom
import SOAS.Abstract.Coalgebra as →□ ; open →□.Sorted
import SOAS.Abstract.Box as □ ; open □.Sorted

open import SOAS.Metatheory.Algebra ⅀F

open Strength ⅀:Str

private
  variable
    Γ : Ctx
    α : T
    𝓐 : Family₂


open Initial 𝕋:Init

open Object ⊥ public renaming (𝐶 to 𝕋 ; ˢ to 𝕋ᵃ)
open MetaAlg 𝕋ᵃ public renaming (𝑎𝑙𝑔 to 𝕒𝕝𝕘 ; 𝑣𝑎𝑟 to 𝕧𝕒𝕣 ; 𝑚𝑣𝑎𝑟 to 𝕞𝕧𝕒𝕣 ; 𝑏𝑜𝑥 to 𝕓𝕠𝕩 ; --𝑙𝑒𝑡𝑏𝑜𝑥 to 𝕝𝕖𝕥𝕓𝕠𝕩 ;
                                  𝑚≈₁ to 𝕞≈₁ ; 𝑚≈₂ to 𝕞≈₂)

module Semantics (𝓐ᵃ : MetaAlg 𝓐) where

  open Morphism (! {𝓐 ⋉ 𝓐ᵃ}) public renaming (𝑓 to 𝕤𝕖𝕞 ; ˢ⇒ to 𝕤𝕖𝕞ᵃ⇒)
  open MetaAlg⇒ 𝕤𝕖𝕞ᵃ⇒ public renaming (⟨𝑎𝑙𝑔⟩ to ⟨𝕒⟩ ; ⟨𝑣𝑎𝑟⟩ to ⟨𝕧⟩ ; ⟨𝑚𝑣𝑎𝑟⟩ to ⟨𝕞⟩ ; ⟨𝑏𝑜𝑥⟩ to ⟨𝕓⟩) --; ⟨𝑙𝑒𝑡𝑏𝑜𝑥⟩ to ⟨𝕝⟩)
  open MetaAlg 𝓐ᵃ
  module 𝓐 = MetaAlg 𝓐ᵃ

  eq : {𝔐 : MCtx} {g h : 𝕋 ⇾̣₂ 𝓐} (gᵃ : MetaAlg⇒ 𝕋ᵃ 𝓐ᵃ g) (hᵃ : MetaAlg⇒ 𝕋ᵃ 𝓐ᵃ h) (t : 𝕋 𝔐 α Γ)
     → g t ≡ h t
  eq {g = g}{h} gᵃ hᵃ t  = !-unique₂ (g ⋉ gᵃ) (h ⋉ hᵃ) {x = t}

  -- The interpretation is equal to any other pointed meta-Λ-algebra
  𝕤𝕖𝕞! : {𝔐 : MCtx} {g : 𝕋 ⇾̣₂ 𝓐}(gᵃ : MetaAlg⇒ 𝕋ᵃ 𝓐ᵃ g)(t : 𝕋 𝔐 α Γ) → 𝕤𝕖𝕞 t ≡ g t
  𝕤𝕖𝕞! {g = g} gᵃ t = !-unique (g ⋉ gᵃ) {x = t}

-- Corollaries: every meta-algebra endo-homomorphism is the identity, including 𝕤𝕖𝕞
eq-id : {𝔐 : MCtx} {g : 𝕋 ⇾̣₂ 𝕋} (gᵃ : MetaAlg⇒ 𝕋ᵃ 𝕋ᵃ g) (t : 𝕋 𝔐 α Γ) →
        g t ≡ t
eq-id gᵃ t = Semantics.eq 𝕋ᵃ gᵃ (idᵃ 𝕋ᵃ) t

𝕤𝕖𝕞-id : {𝔐 : MCtx} {t : 𝕋 𝔐 α Γ} → Semantics.𝕤𝕖𝕞 𝕋ᵃ t ≡ t
𝕤𝕖𝕞-id {t = t} = eq-id (Semantics.𝕤𝕖𝕞ᵃ⇒ 𝕋ᵃ) t
