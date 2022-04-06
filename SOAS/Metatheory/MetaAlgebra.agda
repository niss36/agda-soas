
open import SOAS.Common
import SOAS.Families.Core
import SOAS.Context

-- Families with syntactic structure
module SOAS.Metatheory.MetaAlgebra {T : Set}
  (open SOAS.Families.Core {T})
  (open SOAS.Context {T})
  (⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ)
  (𝔛 : Familyₛ)
  ([_]_ : Ctx → T → T) where

open import SOAS.Families.Build {T}

open import SOAS.Variable {T}
open import SOAS.Construction.Structure as Structure
open import SOAS.Abstract.Hom {T}
import SOAS.Abstract.Coalgebra {T} as →□ ; open →□.Sorted

open import SOAS.Metatheory.Algebra ⅀F
open import Data.Product using (Σ; Σ-syntax)

-- Context Replacement
KF : Ctx → Functor 𝔽amiliesₛ 𝔽amiliesₛ
KF Ψ = record { F₀ = λ Fam α Γ → Fam α Ψ ; F₁ = λ f → f ; identity = refl ; homomorphism = refl ; F-resp-≈ = λ z → z }

K₀ : Ctx → Familyₛ → Familyₛ
K₀ Ψ = Functor.₀ (KF Ψ)

K₁ : (Ψ : Ctx) → {𝒳 𝒴 : Familyₛ} → 𝒳 ⇾̣ 𝒴 → (K₀ Ψ) 𝒳 ⇾̣ (K₀ Ψ) 𝒴
K₁ Ψ = Functor.₁ (KF Ψ)

-- Box
δF : Ctx → Functor 𝔽amiliesₛ 𝔽amiliesₛ
δF Ψ = record { F₀ = λ Fam α Γ → Fam ([ Ψ ] α) Γ ; F₁ = λ f → f ; identity = refl ; homomorphism = refl ; F-resp-≈ = λ z → z }

δ₀ : Ctx → Familyₛ → Familyₛ
δ₀ Ψ = Functor.₀ (δF Ψ)

δ₁ : (Ψ : Ctx) → {𝒳 𝒴 : Familyₛ} → 𝒳 ⇾̣ 𝒴 → (δ₀ Ψ) 𝒳 ⇾̣ (δ₀ Ψ) 𝒴
δ₁ Ψ = Functor.₁ (δF Ψ)

private
  variable
    Γ Δ Π Ψ : Ctx
    α : T

-- A family with support for variables, metavariables, and ⅀-algebra structure
record MetaAlg (𝒜 : Familyₛ) : Set where

  field
    𝑎𝑙𝑔 : ⅀ 𝒜 ⇾̣ 𝒜
    𝑣𝑎𝑟 : ℐ ⇾̣ 𝒜
    𝑚𝑣𝑎𝑟 : 𝔛 ⇾̣ 〖 𝒜 , 𝒜 〗
    𝑏𝑜𝑥 : K₀ Ψ 𝒜 ⇾̣ δ₀ Ψ 𝒜

  -- Congruence in metavariable arguments
  𝑚≈₁ : {𝔪₁ 𝔪₂ : 𝔛 α Π}{σ : Π ~[ 𝒜 ]↝ Γ}
      → 𝔪₁ ≡ 𝔪₂
      → 𝑚𝑣𝑎𝑟 𝔪₁ σ ≡ 𝑚𝑣𝑎𝑟 𝔪₂ σ
  𝑚≈₁ refl = refl

  𝑚≈₂ : {𝔪 : 𝔛 α Π}{σ ς : Π ~[ 𝒜 ]↝ Γ}
      → ({τ : T}(v : ℐ τ Π) → σ v ≡ ς v)
      → 𝑚𝑣𝑎𝑟 𝔪 σ ≡ 𝑚𝑣𝑎𝑟 𝔪 ς
  𝑚≈₂ {𝔪 = 𝔪} p = cong (𝑚𝑣𝑎𝑟 𝔪) (dext p)

-- Meta-algebra homomorphism
record MetaAlg⇒ {𝒜 ℬ : Familyₛ}(𝒜ᵃ : MetaAlg 𝒜)(ℬᵃ : MetaAlg ℬ)
                (f : 𝒜 ⇾̣ ℬ) : Set where
  private module 𝒜 = MetaAlg 𝒜ᵃ
  private module ℬ = MetaAlg ℬᵃ

  field
    ⟨𝑎𝑙𝑔⟩  : {t : ⅀ 𝒜 α Γ} → f (𝒜.𝑎𝑙𝑔 t) ≡ ℬ.𝑎𝑙𝑔 (⅀₁ f t)
    ⟨𝑣𝑎𝑟⟩  : {v : ℐ α Γ} → f (𝒜.𝑣𝑎𝑟 v) ≡ ℬ.𝑣𝑎𝑟 v
    ⟨𝑚𝑣𝑎𝑟⟩ : {𝔪 : 𝔛 α Π}{ε : Π ~[ 𝒜 ]↝ Γ} → f (𝒜.𝑚𝑣𝑎𝑟 𝔪 ε) ≡ ℬ.𝑚𝑣𝑎𝑟 𝔪 (f ∘ ε)
    ⟨𝑏𝑜𝑥⟩ : {b : K₀ Ψ 𝒜 α Γ} → f (𝒜.𝑏𝑜𝑥 {Γ = Γ} b) ≡ ℬ.𝑏𝑜𝑥 (f b)

-- Category of meta-algebras
module MetaAlgebraStructure = Structure 𝔽amiliesₛ MetaAlg

MetaAlgebraCatProps : MetaAlgebraStructure.CategoryProps
MetaAlgebraCatProps = record
  { IsHomomorphism = MetaAlg⇒
  ; id-hom = λ {𝒜}{𝒜ᵃ} → record
    { ⟨𝑎𝑙𝑔⟩ = cong (𝑎𝑙𝑔 𝒜ᵃ) (sym ⅀.identity)
    ; ⟨𝑣𝑎𝑟⟩ = refl
    ; ⟨𝑚𝑣𝑎𝑟⟩ = refl
    ; ⟨𝑏𝑜𝑥⟩ = refl }
  ; comp-hom = λ{ {𝐶ˢ = 𝒜ᵃ}{ℬᵃ}{𝒞ᵃ} g f gᵃ⇒ fᵃ⇒ → record
    { ⟨𝑎𝑙𝑔⟩ = trans (cong g (⟨𝑎𝑙𝑔⟩ fᵃ⇒))
            (trans (⟨𝑎𝑙𝑔⟩  gᵃ⇒)
                    (cong (𝑎𝑙𝑔 𝒞ᵃ) (sym ⅀.homomorphism)))
    ; ⟨𝑣𝑎𝑟⟩ = trans (cong g (⟨𝑣𝑎𝑟⟩ fᵃ⇒)) (⟨𝑣𝑎𝑟⟩ gᵃ⇒)
    ; ⟨𝑚𝑣𝑎𝑟⟩ = trans (cong g (⟨𝑚𝑣𝑎𝑟⟩ fᵃ⇒)) (⟨𝑚𝑣𝑎𝑟⟩ gᵃ⇒)
    ; ⟨𝑏𝑜𝑥⟩ = trans (cong g (⟨𝑏𝑜𝑥⟩ fᵃ⇒)) (⟨𝑏𝑜𝑥⟩ gᵃ⇒)
    }
  }} where open MetaAlg ; open MetaAlg⇒

module MetaAlgProps = MetaAlgebraStructure.CategoryProps MetaAlgebraCatProps

𝕄etaAlgebras : Category 1ℓ 0ℓ 0ℓ
𝕄etaAlgebras = MetaAlgebraStructure.StructCat MetaAlgebraCatProps

module 𝕄etaAlg = Category 𝕄etaAlgebras


MetaAlgebra : Set₁
MetaAlgebra = 𝕄etaAlg.Obj

MetaAlgebra⇒ : MetaAlgebra → MetaAlgebra → Set
MetaAlgebra⇒ = 𝕄etaAlg._⇒_



-- Identity is a meta-algebra homomorphism
idᵃ : {𝒜 : Familyₛ} → (𝒜ᵃ : MetaAlg 𝒜) → MetaAlg⇒ 𝒜ᵃ 𝒜ᵃ id
idᵃ 𝒜ᵃ = record { ⟨𝑎𝑙𝑔⟩ = cong (MetaAlg.𝑎𝑙𝑔 𝒜ᵃ) (sym ⅀.identity)
                ; ⟨𝑣𝑎𝑟⟩ = refl ; ⟨𝑚𝑣𝑎𝑟⟩ = refl; ⟨𝑏𝑜𝑥⟩ = refl }
