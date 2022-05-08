
-- Coalgebraic strength over an endofunctor
module SOAS.Coalgebraic.Strength {T : Set} where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core {T}
open import SOAS.Abstract.Hom {T}
import SOAS.Abstract.Coalgebra {T} as →□ ; open →□.Sorted

open import SOAS.Coalgebraic.Map


private
  variable
    Γ Δ Θ : Ctx
    α : T
    𝔐 : MCtx

-- Pointed coalgebraic strength for a family endofunctor
record Strength (Fᶠ : Functor 𝔽amiliesₛ 𝔽amiliesₛ) : Set₁ where
  open Functor Fᶠ
  open Coalgₚ

  field
    -- Strength transformation that lifts a 𝒫-substitution over an endofunctor F₀
    str : {𝒫 : Familyₛ}(𝒫ᴮ : Coalgₚ 𝒫)(𝒳 : Familyₛ)
        → F₀ 〖 𝒫 , 𝒳 〗 ⇾̣ 〖 𝒫 , F₀ 𝒳 〗

    -- Naturality conditions for the two components
    str-nat₁ : {𝒫 𝒬 𝒳 : Familyₛ}{𝒫ᴮ : Coalgₚ 𝒫}{𝒬ᴮ : Coalgₚ 𝒬}
             → {f : 𝒬 ⇾̣ 𝒫} (fᴮ⇒ : Coalgₚ⇒ 𝒬ᴮ 𝒫ᴮ f)
             → (h : F₀ 〖 𝒫 , 𝒳 〗 α Γ) (σ : Γ ~[ 𝒬 ]↝ Δ)
      → str 𝒫ᴮ 𝒳 h (f ∘ σ)
      ≡ str 𝒬ᴮ 𝒳 (F₁ (λ{ h′ ς → h′ (λ v → f (ς v))}) h) σ

    str-nat₂ : {𝒫 𝒳 𝒴 : Familyₛ}{𝒫ᴮ : Coalgₚ 𝒫}
             → (f : 𝒳 ⇾̣ 𝒴)(h : F₀ 〖 𝒫 , 𝒳 〗 α Γ)(σ : Γ ~[ 𝒫 ]↝ Δ)
      → str 𝒫ᴮ 𝒴 (F₁ (λ{ h′ ς → f (h′ ς)}) h) σ
      ≡ F₁ f (str 𝒫ᴮ 𝒳 h σ)

    -- Unit law
    str-unit : (𝒳 : Familyₛ)(h : F₀ 〖 ℐ , 𝒳 〗 α Γ)
      → str ℐᴮ 𝒳 h id
      ≡ F₁ (i 𝒳) h

    -- Associativity law for a particular pointed coalgebraic map f
    str-assoc  : (𝒳 : Familyₛ){𝒫 𝒬 ℛ : Familyₛ}
                 {𝒫ᴮ : Coalgₚ 𝒫} {𝒬ᴮ : Coalgₚ 𝒬} {ℛᴮ : Coalgₚ ℛ}
                 {f : 𝒫 ⇾̣ 〖 𝒬 , ℛ 〗}
                 (fᶜ : Coalgebraic 𝒫ᴮ 𝒬ᴮ ℛᴮ f) (open Coalgebraic fᶜ)
                 (h : F₀ 〖 ℛ , 𝒳 〗 α Γ)(σ : Γ ~[ 𝒫 ]↝ Δ)(ς : Δ ~[ 𝒬 ]↝ Θ)
      → str ℛᴮ 𝒳 h (λ v → f (σ v) ς)
      ≡ str 𝒬ᴮ 𝒳 (str 〖𝒫,𝒴〗ᴮ 〖 𝒬 , 𝒳 〗 (F₁ (L 𝒬 ℛ 𝒳) h) (f ∘ σ)) ς


  module _ (𝒳 {𝒫 𝒬 ℛ} : Familyₛ) where

    -- Precompose an internal hom by a parametrised map
    precomp : (f : 𝒫 ⇾̣ 〖 𝒬 , ℛ 〗) → 〖 ℛ , 𝒳 〗 ⇾̣ 〖 𝒫 , 〖 𝒬 , 𝒳 〗 〗
    precomp f h σ ς = h (λ v → f (σ v) ς)

    -- Corollary: strength distributes over pointed coalgebraic maps
    str-dist : {𝒫ᴮ : Coalgₚ 𝒫} {𝒬ᴮ : Coalgₚ 𝒬} {ℛᴮ : Coalgₚ ℛ}
               {f : 𝒫 ⇾̣ 〖 𝒬 , ℛ 〗}
               (fᶜ : Coalgebraic 𝒫ᴮ 𝒬ᴮ ℛᴮ f)
               (h : F₀ 〖 ℛ , 𝒳 〗 α Γ)(σ : Γ ~[ 𝒫 ]↝ Δ)(ς : Δ ~[ 𝒬 ]↝ Θ)
      → str ℛᴮ 𝒳 h (λ v → f (σ v) ς)
      ≡ str 𝒬ᴮ 𝒳 (str 𝒫ᴮ 〖 𝒬 , 𝒳 〗 (F₁ (precomp f) h) σ) ς
    str-dist {𝒫ᴮ = 𝒫ᴮ} {𝒬ᴮ} {ℛᴮ} {f} fᶜ h σ ς =
      begin
          str ℛᴮ 𝒳 h (λ v → f (σ v) ς)
      ≡⟨ str-assoc 𝒳 fᶜ h σ ς ⟩
          str 𝒬ᴮ 𝒳 (str 〖𝒫,𝒴〗ᴮ 〖 𝒬 , 𝒳 〗 (F₁ (L 𝒬 ℛ 𝒳) h) (f ∘ σ)) ς
      ≡⟨ cong (λ - → str 𝒬ᴮ 𝒳 - ς) (str-nat₁ fᴮ⇒ (F₁ (L 𝒬 ℛ 𝒳) h) σ) ⟩
          str 𝒬ᴮ 𝒳 (str 𝒫ᴮ 〖 𝒬 , 𝒳 〗 (F₁ 〖 f , 〖 𝒬 , 𝒳 〗 〗ₗ
                                        (F₁ (L 𝒬 ℛ 𝒳) h)) σ) ς
      ≡˘⟨ cong (λ - → str 𝒬ᴮ 𝒳 (str 𝒫ᴮ 〖 𝒬 , 𝒳 〗 - σ) ς) homomorphism ⟩
          str 𝒬ᴮ 𝒳 (str 𝒫ᴮ 〖 𝒬 , 𝒳 〗 (F₁ (precomp f) h) σ) ς
      ∎
      where
      open ≡-Reasoning
      open Coalgebraic fᶜ renaming (ᴮ⇒ to fᴮ⇒)

record Strength₂ (Fᶠ : Functor 𝔽amilies₂ 𝔽amilies₂) : Set₁ where
  open Functor Fᶠ
  open Coalgₚ

  field
    -- Strength transformation that lifts a 𝒫-substitution over an endofunctor F₀
    str : {𝒫 : Family₂}(𝒫ᴮ : {𝔐 : MCtx} → Coalgₚ (𝒫 𝔐))(𝒫₁ : {𝔐 : MCtx} → (f : MCtx → MCtx) → (𝒫 𝔐 ⇾̣ 𝒫 (f 𝔐)))(𝒳 : Family₂)
        → F₀ 〖 𝒫 , 𝒳 〗² ⇾̣₂ 〖 𝒫 , F₀ 𝒳 〗²

    -- Naturality conditions for the two components
    str-nat₁ : {𝒫 𝒬 𝒳 : Family₂}{𝒫ᴮ : {𝔐 : MCtx} → Coalgₚ (𝒫 𝔐)}{𝒫₁ : {𝔐 : MCtx} → (f : MCtx → MCtx) → (𝒫 𝔐 ⇾̣ 𝒫 (f 𝔐))}{𝒬ᴮ : {𝔐 : MCtx} → Coalgₚ (𝒬 𝔐)}{𝒬₁ : {𝔐 : MCtx} → (f : MCtx → MCtx) → (𝒬 𝔐 ⇾̣ 𝒬 (f 𝔐))}
             → {f : 𝒬 ⇾̣₂ 𝒫} (fᴮ⇒ : {𝔐 : MCtx} → Coalgₚ⇒ (𝒬ᴮ {𝔐}) (𝒫ᴮ {𝔐}) (f {𝔐}))
             → (h : F₀ 〖 𝒫 , 𝒳 〗² 𝔐 α Γ) (σ : Γ ~[ 𝒬 𝔐 ]↝ Δ)
      → str 𝒫ᴮ 𝒫₁ 𝒳 h (f ∘ σ)
      ≡ str 𝒬ᴮ 𝒬₁ 𝒳 (F₁ (λ{ h′ ς → h′ (λ v → f (ς v))}) h) σ

    str-nat₂ : {𝒫 𝒳 𝒴 : Family₂}{𝒫ᴮ : {𝔐 : MCtx} → Coalgₚ (𝒫 𝔐)}{𝒫₁ : {𝔐 : MCtx} → (f : MCtx → MCtx) → (𝒫 𝔐 ⇾̣ 𝒫 (f 𝔐))}
             → (f : 𝒳 ⇾̣₂ 𝒴)(h : F₀ 〖 𝒫 , 𝒳 〗² 𝔐 α Γ)(σ : Γ ~[ 𝒫 𝔐 ]↝ Δ)
      → str 𝒫ᴮ 𝒫₁ 𝒴 (F₁ (λ{ h′ ς → f (h′ ς)}) h) σ
      ≡ F₁ f (str 𝒫ᴮ 𝒫₁ 𝒳 h σ)

    -- Unit law
    str-unit : (𝒳 : Family₂)(h : F₀ 〖 (ℐ ᴷ) , 𝒳 〗² 𝔐 α Γ)
      → str ℐᴮ (λ _ → id) 𝒳 h id
      ≡ F₁ (i² 𝒳) h

    -- Associativity law for a particular pointed coalgebraic map f
    -- str-assoc  : (𝒳 : Family₂){𝒫 𝒬 ℛ : Family₂}
    --              {𝒫ᴮ : {𝔐 : MCtx} → Coalgₚ (𝒫 𝔐)} {𝒬ᴮ : {𝔐 : MCtx} → Coalgₚ (𝒬 𝔐)} {ℛᴮ : {𝔐 : MCtx} → Coalgₚ (ℛ 𝔐)}
    --              {𝒫₁ : {𝔐 : MCtx} → (f : MCtx → MCtx) → (𝒫 𝔐 ⇾̣ 𝒫 (f 𝔐))} {𝒬₁ : {𝔐 : MCtx} → (f : MCtx → MCtx) → (𝒬 𝔐 ⇾̣ 𝒬 (f 𝔐))} {ℛ₁ : {𝔐 : MCtx} → (f : MCtx → MCtx) → (ℛ 𝔐 ⇾̣ ℛ (f 𝔐))}
    --              {f : 𝒫 ⇾̣₂ 〖 𝒬 , ℛ 〗²}
    --              (fᶜ : {𝔐 : MCtx} → Coalgebraic (𝒫ᴮ {𝔐}) (𝒬ᴮ {𝔐}) (ℛᴮ {𝔐}) (f {𝔐}))
    --              (h : F₀ 〖 ℛ , 𝒳 〗² 𝔐 α Γ)(σ : Γ ~[ 𝒫 𝔐 ]↝ Δ)(ς : Δ ~[ 𝒬 𝔐 ]↝ Θ)
    --   → str ℛᴮ ℛ₁ 𝒳 h (λ v → f (σ v) ς)
    --   ≡ str 𝒬ᴮ 𝒬₁ 𝒳 (str (λ {𝔐} → Coalgebraic.〖𝒫,𝒴〗ᴮ (fᶜ {𝔐})) (λ {𝔐} f → {!   !} ) 〖 𝒬 , 𝒳 〗² (F₁ (L² 𝒬 ℛ 𝒳) h) (f ∘ σ)) ς
  --
  --
  -- module _ (𝒳 {𝒫 𝒬 ℛ} : Familyₛ) where
  --
  --   -- Precompose an internal hom by a parametrised map
  --   precomp : (f : 𝒫 ⇾̣ 〖 𝒬 , ℛ 〗) → 〖 ℛ , 𝒳 〗 ⇾̣ 〖 𝒫 , 〖 𝒬 , 𝒳 〗 〗
  --   precomp f h σ ς = h (λ v → f (σ v) ς)
  --
  --   -- Corollary: strength distributes over pointed coalgebraic maps
  --   str-dist : {𝒫ᴮ : Coalgₚ 𝒫} {𝒬ᴮ : Coalgₚ 𝒬} {ℛᴮ : Coalgₚ ℛ}
  --              {f : 𝒫 ⇾̣ 〖 𝒬 , ℛ 〗}
  --              (fᶜ : Coalgebraic 𝒫ᴮ 𝒬ᴮ ℛᴮ f)
  --              (h : F₀ 〖 ℛ , 𝒳 〗 α Γ)(σ : Γ ~[ 𝒫 ]↝ Δ)(ς : Δ ~[ 𝒬 ]↝ Θ)
  --     → str ℛᴮ 𝒳 h (λ v → f (σ v) ς)
  --     ≡ str 𝒬ᴮ 𝒳 (str 𝒫ᴮ 〖 𝒬 , 𝒳 〗 (F₁ (precomp f) h) σ) ς
  --   str-dist {𝒫ᴮ = 𝒫ᴮ} {𝒬ᴮ} {ℛᴮ} {f} fᶜ h σ ς =
  --     begin
  --         str ℛᴮ 𝒳 h (λ v → f (σ v) ς)
  --     ≡⟨ str-assoc 𝒳 fᶜ h σ ς ⟩
  --         str 𝒬ᴮ 𝒳 (str 〖𝒫,𝒴〗ᴮ 〖 𝒬 , 𝒳 〗 (F₁ (L 𝒬 ℛ 𝒳) h) (f ∘ σ)) ς
  --     ≡⟨ cong (λ - → str 𝒬ᴮ 𝒳 - ς) (str-nat₁ fᴮ⇒ (F₁ (L 𝒬 ℛ 𝒳) h) σ) ⟩
  --         str 𝒬ᴮ 𝒳 (str 𝒫ᴮ 〖 𝒬 , 𝒳 〗 (F₁ 〖 f , 〖 𝒬 , 𝒳 〗 〗ₗ
  --                                       (F₁ (L 𝒬 ℛ 𝒳) h)) σ) ς
  --     ≡˘⟨ cong (λ - → str 𝒬ᴮ 𝒳 (str 𝒫ᴮ 〖 𝒬 , 𝒳 〗 - σ) ς) homomorphism ⟩
  --         str 𝒬ᴮ 𝒳 (str 𝒫ᴮ 〖 𝒬 , 𝒳 〗 (F₁ (precomp f) h) σ) ς
  --     ∎
  --     where
  --     open ≡-Reasoning
  --     open Coalgebraic fᶜ renaming (ᴮ⇒ to fᴮ⇒)
