
open import SOAS.Common
open import SOAS.Families.Core
open import Categories.Object.Initial
open import SOAS.Coalgebraic.Strength
import SOAS.Context

-- Monoids with ⅀-algebra structure
module SOAS.Metatheory.Monoid {T : Set}
  (open SOAS.Context {T})
  ([_]_ : Ctx → T → T)
  (⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ) (⅀:Str : Strength ⅀F)
  where

open import SOAS.Metatheory.MetaAlgebra {T} [_]_ ⅀F
open import SOAS.Variable
open import SOAS.Construction.Structure as Structure
open import SOAS.Abstract.Hom

open import SOAS.Abstract.Monoid

open import SOAS.Coalgebraic.Map
open import SOAS.Coalgebraic.Monoid

open import SOAS.Metatheory.Algebra {T} ⅀F
open import SOAS.Metatheory.Contextual [_]_

open Strength ⅀:Str

private
  variable
    Γ Δ : Ctx
    α : T

-- Family with compatible monoid and ⅀-algebra structure
record ΣMon (ℳ : Familyₛ) : Set where
  field
    ᵐ : Mon ℳ
    𝑎𝑙𝑔 : ⅀ ℳ ⇾̣ ℳ

  open Mon ᵐ public

  field
    μ⟨𝑎𝑙𝑔⟩ : {σ : Γ ~[ ℳ ]↝ Δ}(t : ⅀ ℳ α Γ)
          → μ (𝑎𝑙𝑔 t) σ ≡ 𝑎𝑙𝑔 (str ᴮ ℳ (⅀₁ μ t) σ)

record ΣMon⇒ {ℳ 𝒩 : Familyₛ}(ℳᴹ : ΣMon ℳ)(𝒩ᴹ : ΣMon 𝒩)
             (f : ℳ ⇾̣ 𝒩) : Set where
  private module ℳ = ΣMon ℳᴹ
  private module 𝒩 = ΣMon 𝒩ᴹ
  field
    ᵐ⇒ : Mon⇒ ℳ.ᵐ 𝒩.ᵐ f
    ⟨𝑎𝑙𝑔⟩ : {t : ⅀ ℳ α Γ} → f (ℳ.𝑎𝑙𝑔 t) ≡ 𝒩.𝑎𝑙𝑔 (⅀₁ f t)

  open Mon⇒ ᵐ⇒ public

-- Category of Σ-monoids
module ΣMonoidStructure = Structure 𝔽amiliesₛ ΣMon

ΣMonoidCatProps : ΣMonoidStructure.CategoryProps
ΣMonoidCatProps = record
  { IsHomomorphism = ΣMon⇒
  ; id-hom = λ {ℳ}{ℳᴹ} → record
    { ᵐ⇒ = AsMonoid⇒.ᵐ⇒ 𝕄on.id
    ; ⟨𝑎𝑙𝑔⟩ = cong (ΣMon.𝑎𝑙𝑔 ℳᴹ) (sym ⅀.identity)
    }
  ; comp-hom = λ{ {𝐸ˢ = 𝒪ᴹ} g f record { ᵐ⇒ = gᵐ⇒ ; ⟨𝑎𝑙𝑔⟩ = g⟨𝑎𝑙𝑔⟩ }
                      record { ᵐ⇒ = fᵐ⇒ ; ⟨𝑎𝑙𝑔⟩ = f⟨𝑎𝑙𝑔⟩ } → record
    { ᵐ⇒ = AsMonoid⇒.ᵐ⇒ ((g ⋉ gᵐ⇒) 𝕄on.∘ (f ⋉ fᵐ⇒))
    ; ⟨𝑎𝑙𝑔⟩ = trans (cong g f⟨𝑎𝑙𝑔⟩) (trans g⟨𝑎𝑙𝑔⟩
                   (cong (ΣMon.𝑎𝑙𝑔 𝒪ᴹ) (sym ⅀.homomorphism))) } }
  }

Σ𝕄onoids : Category 1ℓ 0ℓ 0ℓ
Σ𝕄onoids = ΣMonoidStructure.StructCat ΣMonoidCatProps

module Σ𝕄on = Category Σ𝕄onoids

ΣMonoid : Set₁
ΣMonoid = Σ𝕄on.Obj

ΣMonoid⇒ : ΣMonoid → ΣMonoid → Set
ΣMonoid⇒ = Σ𝕄on._⇒_

module FreeΣMonoid = ΣMonoidStructure.Free ΣMonoidCatProps


-- Family with compatible monoid, ⅀-algebra and box-letbox structure
record ΣMon₂ (𝓜 : Family₂) : Set where
  field
    ᵐ : Mon₂ 𝓜
    𝑎𝑙𝑔 : (⅀ ²) 𝓜 ⇾̣₂ 𝓜
    𝑏𝑜𝑥 : (B ²) 𝓜 ⇾̣₂ 𝓜
    -- 𝑙𝑒𝑡𝑏𝑜𝑥 : LB 𝓜 ⇾̣₂ 𝓜

  open Mon₂ ᵐ public

  field
    μ⟨𝑎𝑙𝑔⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓜 𝔐 ]↝ Δ}(t : ⅀ (𝓜 𝔐) α Γ)
          → μ (𝑎𝑙𝑔 t) σ ≡ 𝑎𝑙𝑔 (str ᴮ (𝓜 𝔐) (⅀₁ μ t) σ)
    μ⟨𝑏𝑜𝑥⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓜 𝔐 ]↝ Δ}{Ψ : Ctx}(t : B (𝓜 𝔐) α Γ)
          → μ (𝑏𝑜𝑥 t) σ ≡ 𝑏𝑜𝑥 (BF:Str.str ᴮ (𝓜 𝔐) (B₁ μ {α}{Γ} t) σ)

record ΣMon₂⇒ {𝓜 𝓝 : Family₂}(𝓜ᴹ : ΣMon₂ 𝓜)(𝓝ᴹ : ΣMon₂ 𝓝)
             (f : 𝓜 ⇾̣₂ 𝓝) : Set where
  private module 𝓜 = ΣMon₂ 𝓜ᴹ
  private module 𝓝 = ΣMon₂ 𝓝ᴹ
  field
    ᵐ⇒ : Mon₂⇒ 𝓜.ᵐ 𝓝.ᵐ f
    ⟨𝑎𝑙𝑔⟩ : {𝔐 : MCtx}{t : ⅀ (𝓜 𝔐) α Γ} → f (𝓜.𝑎𝑙𝑔 t) ≡ 𝓝.𝑎𝑙𝑔 (⅀₁ f t)
    ⟨𝑏𝑜𝑥⟩ : {𝔐 : MCtx}{b : B (𝓜 𝔐) α Γ} → f (𝓜.𝑏𝑜𝑥 {Γ = Γ} b) ≡ 𝓝.𝑏𝑜𝑥 (B₁ f {α}{Γ} b)
    -- ⟨𝑙𝑒𝑡𝑏𝑜𝑥⟩ : {𝔐 : MCtx}{lb : LB 𝓜 𝔐 α Γ} → f (𝓜.𝑙𝑒𝑡𝑏𝑜𝑥 lb) ≡ 𝓝.𝑙𝑒𝑡𝑏𝑜𝑥 {! LB₁ f lb  !} --f {𝔐}{α}{Γ} (𝓜.𝑙𝑒𝑡𝑏𝑜𝑥 lb) ≡ 𝓝.𝑙𝑒𝑡𝑏𝑜𝑥 {𝔐}{α}{Γ} (LB₁ f lb) --f (𝓜.𝑙𝑒𝑡𝑏𝑜𝑥 lb) ≡ 𝓝.𝑙𝑒𝑡𝑏𝑜𝑥 (LB₁ f lb)

  open Mon₂⇒ ᵐ⇒ public

-- Category of Σ-monoids
module ΣMonoidStructure₂ = Structure 𝔽amilies₂ ΣMon₂

ΣMonoidCatProps₂ : ΣMonoidStructure₂.CategoryProps
ΣMonoidCatProps₂ = record
  { IsHomomorphism = ΣMon₂⇒
  ; id-hom = λ {𝓜}{𝓜ᴹ} → record
    { ᵐ⇒ = AsMonoid₂⇒.ᵐ⇒ 𝕄on₂.id
    ; ⟨𝑎𝑙𝑔⟩ = cong (ΣMon₂.𝑎𝑙𝑔 𝓜ᴹ) (sym ⅀.identity)
    ; ⟨𝑏𝑜𝑥⟩ = refl
    }
  ; comp-hom = λ{ {𝐸ˢ = 𝒪ᴹ} g f record { ᵐ⇒ = gᵐ⇒ ; ⟨𝑎𝑙𝑔⟩ = g⟨𝑎𝑙𝑔⟩ ; ⟨𝑏𝑜𝑥⟩ = g⟨𝑏𝑜𝑥⟩ }
                      record { ᵐ⇒ = fᵐ⇒ ; ⟨𝑎𝑙𝑔⟩ = f⟨𝑎𝑙𝑔⟩ ; ⟨𝑏𝑜𝑥⟩ = f⟨𝑏𝑜𝑥⟩ } → record
    { ᵐ⇒ = AsMonoid₂⇒.ᵐ⇒ ((g ⋉ gᵐ⇒) 𝕄on₂.∘ (f ⋉ fᵐ⇒))
    ; ⟨𝑎𝑙𝑔⟩ = trans (cong g f⟨𝑎𝑙𝑔⟩) (trans g⟨𝑎𝑙𝑔⟩
                   (cong (ΣMon₂.𝑎𝑙𝑔 𝒪ᴹ) (sym ⅀.homomorphism)))
    ; ⟨𝑏𝑜𝑥⟩ = trans (cong g f⟨𝑏𝑜𝑥⟩) (trans g⟨𝑏𝑜𝑥⟩ refl)
    } }
  }

Σ𝕄onoids₂ : Category 1ℓ 0ℓ 0ℓ
Σ𝕄onoids₂ = ΣMonoidStructure₂.StructCat ΣMonoidCatProps₂

module Σ𝕄on₂ = Category Σ𝕄onoids₂

ΣMonoid₂ : Set₁
ΣMonoid₂ = Σ𝕄on₂.Obj

ΣMonoid₂⇒ : ΣMonoid₂ → ΣMonoid₂ → Set
ΣMonoid₂⇒ = Σ𝕄on₂._⇒_

module FreeΣMonoid₂ = ΣMonoidStructure₂.Free ΣMonoidCatProps₂
