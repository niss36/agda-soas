
-- Closed monoid in the skew-closed category of families
module SOAS.Abstract.Monoid {T : Set} where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.ContextMaps.Combinators

open import SOAS.Construction.Structure as Structure

open import SOAS.Abstract.Hom {T}
open import SOAS.Abstract.Coalgebra using (module Sorted) ; open Sorted
open import SOAS.Families.Core {T}

open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open import SOAS.Coalgebraic.Map {T}
open import SOAS.Coalgebraic.Lift {T}

private
  variable
    Γ Δ Θ : Ctx
    α β γ : T

record Mon (𝒳 : Familyₛ) : Set where
  field
    η : ℐ ⇾̣ 𝒳
    μ : 𝒳 ⇾̣ 〖 𝒳 , 𝒳 〗

    lunit : {σ : Γ ~[ 𝒳 ]↝ Δ}{v : ℐ α Γ}
          → μ (η v) σ ≡ σ v
    runit : {t : 𝒳 α Γ} → μ t η ≡ t
    assoc : {σ : Γ ~[ 𝒳 ]↝ Δ}{ς : Δ ~[ 𝒳 ]↝ Θ} {t : 𝒳 α Γ}
          → μ (μ t σ) ς ≡ μ t (λ v → μ (σ v) ς)

  -- Congruence in both arguments of the multiplication
  μ≈₁ : {t₁ t₂ : 𝒳 α Γ}{σ : Γ ~[ 𝒳 ]↝ Δ}
      → t₁ ≡ t₂
      → μ t₁ σ ≡ μ t₂ σ
  μ≈₁ refl = refl

  μ≈₂ : {t : 𝒳 α Γ}{σ ς : Γ ~[ 𝒳 ]↝ Δ}
      → ({τ : T}{v : ℐ τ Γ} → σ v ≡ ς v)
      → μ t σ ≡ μ t ς
  μ≈₂ {t = t} p = cong (μ t) (dext′ p)

  -- Monoids are pointed coalgebras
  ᵇ : Coalg 𝒳
  ᵇ = record { r = λ t ρ →  μ t (η ∘ ρ) ; counit = runit
    ; comult = λ { {t = t} → sym (trans assoc (μ≈₂ lunit)) } }

  ᴮ : Coalgₚ 𝒳
  ᴮ = record { ᵇ = ᵇ ; η = η ; r∘η = lunit }

  -- Single-variable substitution
  [_/] : 𝒳 α Γ → 𝒳 β (α ∙ Γ) → 𝒳 β Γ
  [ s /] t = μ t (add 𝒳 s η)

  -- Substitution for second variable
  [_/]′ : 𝒳 α Γ → 𝒳 γ (β ∙ α ∙ Γ) → 𝒳 γ (β ∙ Γ)
  [ s /]′ t = μ t (lift₁ ᴮ (add 𝒳 s η))

  -- Substitution for top two variables
  [_,_/]₂ : 𝒳 α Γ → 𝒳 β Γ → 𝒳 γ (α ∙ β ∙ Γ) → 𝒳 γ Γ
  [ s₁ , s₂ /]₂ t = μ t (add 𝒳 s₁ (add 𝒳 s₂ η))


  open Coalgₚ ᴮ public using (r ; r∘η)

  -- Multiplication is coalgebraic map
  μᶜ : Coalgebraic ᴮ ᴮ ᴮ μ
  μᶜ = record { r∘f = assoc ; f∘r = trans assoc (μ≈₂ lunit) ; f∘η = lunit }


-- Monoid homomorphisms
record Mon⇒ {𝒳 𝒴 : Familyₛ}(𝒳ᵐ : Mon 𝒳)(𝒴ᵐ : Mon 𝒴)
               (f : 𝒳 ⇾̣ 𝒴) : Set where

  private module 𝒳 = Mon 𝒳ᵐ
  private module 𝒴 = Mon 𝒴ᵐ

  field
    ⟨η⟩ : {v : ℐ α Γ} → f (𝒳.η v) ≡ 𝒴.η v
    ⟨μ⟩ : {σ : Γ ~[ 𝒳 ]↝ Δ}{t : 𝒳 α Γ}
        → f (𝒳.μ t σ) ≡ 𝒴.μ (f t) (f ∘ σ)

  ᵇ⇒ : Coalg⇒ 𝒳.ᵇ 𝒴.ᵇ f
  ᵇ⇒ = record { ⟨r⟩ = trans ⟨μ⟩ (𝒴.μ≈₂ ⟨η⟩) }

  ᴮ⇒ : Coalgₚ⇒ 𝒳.ᴮ 𝒴.ᴮ f
  ᴮ⇒ = record { ᵇ⇒ = ᵇ⇒ ; ⟨η⟩ = ⟨η⟩ }

  -- Preservation of multiplication and unit implies the semantic substitution
  -- lemma for single- and double-variable substitution
  sub-lemma : (s : 𝒳 α Γ)(t : 𝒳 β (α ∙ Γ)) →
              f (𝒳.[ s /] t) ≡ 𝒴.[ f s /] (f t)
  sub-lemma s t = trans ⟨μ⟩ (cong (𝒴.μ (f t))
                        (dext λ{ new → refl ; (old y) → ⟨η⟩}))

  sub-lemma₂ : (s₁ : 𝒳 α Γ)(s₂ : 𝒳 β Γ)(t : 𝒳 γ (α ∙ β ∙ Γ)) →
               f (𝒳.[ s₁ , s₂ /]₂ t) ≡ 𝒴.[ f s₁ , f s₂ /]₂ (f t)
  sub-lemma₂ s₁ s₂ t = trans ⟨μ⟩ (cong (𝒴.μ (f t))
                             (dext λ{ new → refl ; (old new) → refl
                                    ; (old (old y)) → ⟨η⟩}))


module MonoidStructure = Structure 𝔽amiliesₛ Mon

-- Category of substitution monoids
𝕄onoids : Category 1ℓ 0ℓ 0ℓ
𝕄onoids = MonoidStructure.StructCat record
  { IsHomomorphism = Mon⇒
  ; id-hom = record { ⟨η⟩ = refl ; ⟨μ⟩ = refl }
  ; comp-hom = λ g f gᵐ⇒ fᵐ⇒ → record
    { ⟨η⟩ = trans (cong g (⟨η⟩ fᵐ⇒)) (⟨η⟩ gᵐ⇒)
    ; ⟨μ⟩ = trans (cong g (⟨μ⟩ fᵐ⇒)) (⟨μ⟩ gᵐ⇒)
    }
  } where open Mon⇒

module 𝕄on = Category 𝕄onoids

Monoid : Set₁
Monoid = 𝕄on.Obj

Monoid⇒ : Monoid → Monoid → Set
Monoid⇒ = 𝕄on._⇒_

module AsMonoid (ℳᵐ : Monoid) where
  open Object ℳᵐ renaming (𝐶 to ℳ; ˢ to ᵐ) public
  open Mon ᵐ public



module AsMonoid⇒ {ℳᵐ 𝒩ᵐ : Monoid} (fᵐ⇒ : Monoid⇒ ℳᵐ 𝒩ᵐ) where
  open Morphism fᵐ⇒ renaming (𝑓 to f ; ˢ⇒ to ᵐ⇒) public
  open Mon⇒ ᵐ⇒ public




record Mon₂ (𝓧 : Family₂) : Set where
  field
    η : (ℐ ᴷ) ⇾̣₂ 𝓧
    μ : 𝓧 ⇾̣₂ 〖 𝓧 , 𝓧 〗²

    lunit : {𝔐 : MCtx}{σ : Γ ~[ 𝓧 𝔐 ]↝ Δ}{v : ℐ α Γ}
          → μ (η v) σ ≡ σ v
    runit : {𝔐 : MCtx}{t : 𝓧 𝔐 α Γ} → μ t η ≡ t
    assoc : {𝔐 : MCtx}{σ : Γ ~[ 𝓧 𝔐 ]↝ Δ}{ς : Δ ~[ 𝓧 𝔐 ]↝ Θ} {t : 𝓧 𝔐 α Γ}
          → μ (μ t σ) ς ≡ μ t (λ v → μ (σ v) ς)

  -- Congruence in both arguments of the multiplication
  μ≈₁ : {𝔐 : MCtx}{t₁ t₂ : 𝓧 𝔐 α Γ}{σ : Γ ~[ 𝓧 𝔐 ]↝ Δ}
      → t₁ ≡ t₂
      → μ t₁ σ ≡ μ t₂ σ
  μ≈₁ refl = refl

  μ≈₂ : {𝔐 : MCtx}{t : 𝓧 𝔐 α Γ}{σ ς : Γ ~[ 𝓧 𝔐 ]↝ Δ}
      → ({τ : T}{v : ℐ τ Γ} → σ v ≡ ς v)
      → μ t σ ≡ μ t ς
  μ≈₂ {t = t} p = cong (μ t) (dext′ p)

  -- Monoids are pointed coalgebras
  ᵇ : {𝔐 : MCtx} → Coalg (𝓧 𝔐)
  ᵇ = record { r = λ t ρ →  μ t (η ∘ ρ) ; counit = runit
    ; comult = λ { {t = t} → sym (trans assoc (μ≈₂ lunit)) } }

  ᴮ : {𝔐 : MCtx} → Coalgₚ (𝓧 𝔐)
  ᴮ = record { ᵇ = ᵇ ; η = η ; r∘η = lunit }

  -- Single-variable substitution
  [_/] : {𝔐 : MCtx} → 𝓧 𝔐 α Γ → 𝓧 𝔐 β (α ∙ Γ) → 𝓧 𝔐 β Γ
  [_/] {𝔐 = 𝔐} s t = μ t (add (𝓧 𝔐) s η)

  -- Substitution for second variable
  [_/]′ : {𝔐 : MCtx} → 𝓧 𝔐 α Γ → 𝓧 𝔐 γ (β ∙ α ∙ Γ) → 𝓧 𝔐 γ (β ∙ Γ)
  [_/]′ {𝔐 = 𝔐} s t = μ t (lift₁ ᴮ (add (𝓧 𝔐) s η))

  -- Substitution for top two variables
  [_,_/]₂ : {𝔐 : MCtx} → 𝓧 𝔐 α Γ → 𝓧 𝔐 β Γ → 𝓧 𝔐 γ (α ∙ β ∙ Γ) → 𝓧 𝔐 γ Γ
  [_,_/]₂ {𝔐 = 𝔐} s₁ s₂ t = μ t (add (𝓧 𝔐) s₁ (add (𝓧 𝔐) s₂ η))


  open module - {𝔐} = Coalgₚ (ᴮ {𝔐}) public using (r ; r∘η)

  -- Multiplication is coalgebraic map
  μᶜ : {𝔐 : MCtx} → Coalgebraic (ᴮ {𝔐}) (ᴮ {𝔐}) (ᴮ {𝔐}) μ
  μᶜ = record { r∘f = assoc ; f∘r = trans assoc (μ≈₂ lunit) ; f∘η = lunit }


-- Monoid homomorphisms
record Mon₂⇒ {𝓧 𝓨 : Family₂}(𝓧ᵐ : Mon₂ 𝓧)(𝓨ᵐ : Mon₂ 𝓨)
               (f : 𝓧 ⇾̣₂ 𝓨) : Set where

  private module 𝓧 = Mon₂ 𝓧ᵐ
  private module 𝓨 = Mon₂ 𝓨ᵐ

  field
    ⟨η⟩ : {𝔐 : MCtx}{v : ℐ α Γ} → f {𝔐} (𝓧.η v) ≡ 𝓨.η v
    ⟨μ⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓧 𝔐 ]↝ Δ}{t : 𝓧 𝔐 α Γ}
        → f (𝓧.μ t σ) ≡ 𝓨.μ (f t) (f ∘ σ)

  ᵇ⇒ : {𝔐 : MCtx} → Coalg⇒ (𝓧.ᵇ {𝔐}) (𝓨.ᵇ {𝔐}) f
  ᵇ⇒ = record { ⟨r⟩ = trans ⟨μ⟩ (𝓨.μ≈₂ ⟨η⟩) }

  ᴮ⇒ : {𝔐 : MCtx} → Coalgₚ⇒ (𝓧.ᴮ {𝔐}) (𝓨.ᴮ {𝔐}) f
  ᴮ⇒ = record { ᵇ⇒ = ᵇ⇒ ; ⟨η⟩ = ⟨η⟩ }

  -- Preservation of multiplication and unit implies the semantic substitution
  -- lemma for single- and double-variable substitution
  sub-lemma : {𝔐 : MCtx}(s : 𝓧 𝔐 α Γ)(t : 𝓧 𝔐 β (α ∙ Γ)) →
              f (𝓧.[ s /] t) ≡ 𝓨.[ f s /] (f t)
  sub-lemma s t = trans ⟨μ⟩ (cong (𝓨.μ (f t))
                        (dext λ{ new → refl ; (old y) → ⟨η⟩}))

  sub-lemma₂ : {𝔐 : MCtx}(s₁ : 𝓧 𝔐 α Γ)(s₂ : 𝓧 𝔐 β Γ)(t : 𝓧 𝔐 γ (α ∙ β ∙ Γ)) →
               f (𝓧.[ s₁ , s₂ /]₂ t) ≡ 𝓨.[ f s₁ , f s₂ /]₂ (f t)
  sub-lemma₂ s₁ s₂ t = trans ⟨μ⟩ (cong (𝓨.μ (f t))
                             (dext λ{ new → refl ; (old new) → refl
                                    ; (old (old y)) → ⟨η⟩}))


module MonoidStructure₂ = Structure 𝔽amilies₂ Mon₂

-- Category of substitution monoids
𝕄onoids₂ : Category 1ℓ 0ℓ 0ℓ
𝕄onoids₂ = MonoidStructure₂.StructCat record
  { IsHomomorphism = Mon₂⇒
  ; id-hom = record { ⟨η⟩ = refl ; ⟨μ⟩ = refl }
  ; comp-hom = λ g f gᵐ⇒ fᵐ⇒ → record
    { ⟨η⟩ = trans (cong g (⟨η⟩ fᵐ⇒)) (⟨η⟩ gᵐ⇒)
    ; ⟨μ⟩ = trans (cong g (⟨μ⟩ fᵐ⇒)) (⟨μ⟩ gᵐ⇒)
    }
  } where open Mon₂⇒

module 𝕄on₂ = Category 𝕄onoids₂

Monoid₂ : Set₁
Monoid₂ = 𝕄on₂.Obj

Monoid₂⇒ : Monoid₂ → Monoid₂ → Set
Monoid₂⇒ = 𝕄on₂._⇒_

module AsMonoid₂ (𝓜ᵐ : Monoid₂) where
  open Object 𝓜ᵐ renaming (𝐶 to 𝓜; ˢ to ᵐ) public
  open Mon₂ ᵐ public



module AsMonoid₂⇒ {𝓜ᵐ 𝓝ᵐ : Monoid₂} (fᵐ⇒ : Monoid₂⇒ 𝓜ᵐ 𝓝ᵐ) where
  open Morphism fᵐ⇒ renaming (𝑓 to f ; ˢ⇒ to ᵐ⇒) public
  open Mon₂⇒ ᵐ⇒ public
