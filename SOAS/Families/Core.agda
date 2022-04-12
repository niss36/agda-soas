
-- Category of indexed families
module SOAS.Families.Core {T : Set} where

open import SOAS.Common
open import SOAS.Context {T}
open import SOAS.Sorting


-- | Unsorted

-- Sets indexed by a context
Family : Set₁
Family = Ctx → Set

-- Indexed functions between families
_⇾_ : Family → Family → Set
X ⇾ Y = ∀{Γ : Ctx} → X Γ → Y Γ
infixr 10 _⇾_

-- Category of indexed families of sets and indexed functions between them
𝔽amilies : Category 1ℓ 0ℓ 0ℓ
𝔽amilies = categoryHelper record
  { Obj = Family
  ; _⇒_ = _⇾_
  ; _≈_ = λ {X}{Y} f g → ∀{Γ : Ctx}{x : X Γ} → f x ≡ g x
  ; id = id
  ; _∘_ = λ g f → g ∘ f
  ; assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; equiv = record { refl = refl ; sym = λ p → sym p ; trans = λ p q → trans p q }
  ; ∘-resp-≈ = λ where {f = f} p q → trans (cong f q) p
  }
module 𝔽am = Category 𝔽amilies


-- | Sorted

-- Category of sorted families
𝔽amiliesₛ : Category 1ℓ 0ℓ 0ℓ
𝔽amiliesₛ = 𝕊orted {T} 𝔽amilies
module 𝔽amₛ = Category 𝔽amiliesₛ

-- Type of sorted families
Familyₛ : Set₁
Familyₛ = 𝔽amₛ.Obj

-- Maps between sorted families
_⇾̣_ : Familyₛ → Familyₛ → Set
_⇾̣_ = 𝔽amₛ._⇒_
infixr 10 _⇾̣_

-- Turn sorted family into unsorted by internally quantifying over the sort
∀[_] : Familyₛ → Family
∀[ 𝒳 ] Γ = {τ : T} → 𝒳 τ Γ


-- | Metavariable contexts

-- Inductive construction of context- and type-indexed sets
data MCtx : Set where
  ⁅⁆      : MCtx
  ⁅_⊩ₙ_⁆_ : (Π : Ctx) → (τ : T) → MCtx → MCtx
infixr 7 ⁅_⊩ₙ_⁆_

-- Pattern synonym for parameterless elements and final elements
infixr 10 ⁅_⁆̣ ⁅_⊩ₙ_⁆̣
infixr 7 ⁅_⁆_ ⁅_⊩_⁆_ ⁅_·_⊩_⁆_ ⁅_⊩_⁆̣ ⁅_·_⊩_⁆̣ _⁅_⊩ₙ_⁆
pattern ⁅_⁆̣ α = ⁅ ∅ ⊩ₙ α ⁆ ⁅⁆
pattern ⁅_⊩ₙ_⁆̣ Π α = ⁅ Π ⊩ₙ α ⁆ ⁅⁆
pattern ⁅_⁆_ τ 𝔐 = ⁅ ∅ ⊩ₙ τ ⁆ 𝔐
pattern ⁅_⊩_⁆_ τ α 𝔐 = ⁅ ⌊ τ ⌋ ⊩ₙ α ⁆ 𝔐
pattern ⁅_·_⊩_⁆_ τ₁ τ₂ α 𝔐 = ⁅ ⌊ τ₁ ∙ τ₂ ⌋ ⊩ₙ α ⁆ 𝔐
pattern ⁅_⊩_⁆̣ τ α = ⁅ ⌊ τ ⌋ ⊩ₙ α ⁆ ⁅⁆
pattern ⁅_·_⊩_⁆̣ τ₁ τ₂ α = ⁅ ⌊ τ₁ ∙ τ₂ ⌋ ⊩ₙ α ⁆ ⁅⁆

-- Add type-context pair to the end of the metavariable context
_⁅_⊩ₙ_⁆ : MCtx → Ctx → T → MCtx
⁅⁆              ⁅ Γ ⊩ₙ α ⁆ = ⁅ Γ ⊩ₙ α ⁆̣
(⁅ Π ⊩ₙ τ ⁆ 𝔐) ⁅ Γ ⊩ₙ α ⁆ = ⁅ Π ⊩ₙ τ ⁆ (𝔐 ⁅ Γ ⊩ₙ α ⁆)

private
  variable
    Γ Δ : Ctx
    α β : T
    𝔐 : MCtx

-- Membership of metavariable contexts
data _⊩_∈_ : Ctx → T → MCtx → Set where
  ↓ : Γ ⊩ α ∈ (⁅ Γ ⊩ₙ α ⁆ 𝔐)
  ↑_ : Γ ⊩ α ∈ 𝔐 → Γ ⊩ α ∈ (⁅ Δ ⊩ₙ β ⁆ 𝔐)

infixr 220 ↑_

-- Metavariable context can be interpreted as a family via the membership
∥_∥ : MCtx → Familyₛ
∥ 𝔐 ∥ α Γ = Γ ⊩ α ∈ 𝔐
infixr 60 ∥_∥

_▷_ : MCtx → (Familyₛ → Familyₛ) → Familyₛ
𝔐 ▷ 𝒳 = 𝒳 ∥ 𝔐 ∥
infix 4 _▷_


-- | Sorted with metavariable context
𝔽amilies₂ : Category 1ℓ 0ℓ 0ℓ
𝔽amilies₂ = 𝕊orted {MCtx} 𝔽amiliesₛ
module 𝔽am₂ = Category 𝔽amilies₂

Family₂ : Set₁
Family₂ = 𝔽am₂.Obj

-- Maps between sorted families
_⇾̣₂_ : Family₂ → Family₂ → Set
_⇾̣₂_ = 𝔽am₂._⇒_
infixr 10 _⇾̣₂_

_² : (Familyₛ → Familyₛ) → (Family₂ → Family₂)
_² = sorted {MCtx}

_₂ : (Familyₛ → Familyₛ → Familyₛ) → (Family₂ → Family₂ → Family₂)
_₂ = sorted₂ {MCtx}

_ᴷ : Familyₛ → Family₂
_ᴷ 𝒜 𝔐 = 𝒜
