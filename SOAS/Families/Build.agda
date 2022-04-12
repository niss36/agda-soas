
-- Operators for combining and building families
module SOAS.Families.Build {T : Set} where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Sorting {T}
open import SOAS.Families.Core {T}


-- Generalised sums and pattern matching
data +₂ (A B : Set) : Set where
  _₁ : A → +₂ A B
  _₂ : B → +₂ A B

data +₃ (A B C : Set) : Set where
  _₁ : A → +₃ A B C
  _₂ : B → +₃ A B C
  _₃ : C → +₃ A B C

data +₄ (A B C D : Set) : Set where
  _₁ : A → +₄ A B C D
  _₂ : B → +₄ A B C D
  _₃ : C → +₄ A B C D
  _₄ : D → +₄ A B C D

infixr 60 _₁
infixr 60 _₂
infixr 60 _₃
infixr 60 _₄

₂| : {A B : Set}{X : Set} → (A → X) → (B → X) → (+₂ A B → X)
₂| f g (a ₁) = f a
₂| f g (b ₂) = g b

₃| : {A B C : Set}{X : Set} → (A → X) → (B → X) → (C → X) → (+₃ A B C → X)
₃| f g h (a ₁) = f a
₃| f g h (b ₂) = g b
₃| f g h (c ₃) = h c

₄| : {A B C D : Set}{X : Set} → (A → X) → (B → X) → (C → X) → (D → X) → (+₄ A B C D → X)
₄| f g h e (a ₁) = f a
₄| f g h e (b ₂) = g b
₄| f g h e (c ₃) = h c
₄| f g h e (d ₄) = e d


pattern _ₛ 𝔪 = 𝔪 ₁
pattern _ₘ 𝔪 = 𝔪 ₂
infixr 60 _ₛ
infixr 60 _ₘ

-- Empty and unit families

data Ø : Familyₛ where

data _⊪_ (Γ : Ctx)(α : T) : Familyₛ where
  ● : (Γ ⊪ α) α Γ

⊪_ : T → Familyₛ
⊪ α = ∅ ⊪ α

infix 20 _⊪_
infix 20 ⊪_


-- Sum of families

infix 10 _⊹_
infix 10 _⊹_⊹_
infix 10 _⊹_⊹_⊹_

_⊹_ : Familyₛ → Familyₛ → Familyₛ
(𝒳 ⊹ 𝒴) α Γ = +₂ (𝒳 α Γ) (𝒴 α Γ)

_⊹₁_ : {𝒳₁ 𝒳₂ 𝒴₁ 𝒴₂ : Familyₛ} → (𝒳₁ ⇾̣ 𝒳₂) → (𝒴₁ ⇾̣ 𝒴₂)
     → (𝒳₁ ⊹ 𝒴₁) ⇾̣ (𝒳₂ ⊹ 𝒴₂)
(f ⊹₁ g) (x ₁) = (f x) ₁
(f ⊹₁ g) (y ₂) = (g y) ₂

_⊹_⊹_ : Familyₛ → Familyₛ → Familyₛ → Familyₛ
(𝒳 ⊹ 𝒴 ⊹ 𝒵) α Γ = +₃ (𝒳 α Γ) (𝒴 α Γ) (𝒵 α Γ)

_⊹_⊹_⊹_ : Familyₛ → Familyₛ → Familyₛ → Familyₛ → Familyₛ
(𝒳 ⊹ 𝒴 ⊹ 𝒵 ⊹ 𝒲) α Γ = +₄ (𝒳 α Γ) (𝒴 α Γ) (𝒵 α Γ) (𝒲 α Γ)
