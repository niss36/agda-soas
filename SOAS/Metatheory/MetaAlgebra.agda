
open import SOAS.Common
import SOAS.Families.Core
import SOAS.Context

-- Families with syntactic structure
module SOAS.Metatheory.MetaAlgebra {T : Set}
  (open SOAS.Context {T})
  ([_]_ : Ctx → T → T)
  (open SOAS.Families.Core {T})
  (⅀F : Functor 𝔽amiliesₛ 𝔽amiliesₛ) where

open import SOAS.Variable {T}
open import SOAS.Construction.Structure as Structure
open import SOAS.Abstract.Hom {T}
import SOAS.Abstract.Coalgebra {T} as →□ ; open →□.Sorted

open import SOAS.Metatheory.Algebra ⅀F
open import SOAS.Metatheory.Contextual [_]_

private
  variable
    Γ Δ Π Ψ : Ctx
    α : T
    𝔐 : MCtx

-- A family with support for variables, metavariables, and ⅀-algebra structure
record MetaAlg (𝓐 : Family₂) : Set where

  field
    𝑎𝑙𝑔 : (⅀ ²) 𝓐 ⇾̣₂ 𝓐
    𝑣𝑎𝑟 : (ℐ ᴷ) ⇾̣₂ 𝓐
    𝑚𝑣𝑎𝑟 : ∥_∥ ⇾̣₂ 〖 𝓐 , 𝓐 〗²
    𝑏𝑜𝑥 : (B ²) 𝓐 ⇾̣₂ 𝓐
    𝑙𝑒𝑡𝑏𝑜𝑥 : LB 𝓐 ⇾̣₂ 𝓐

  -- Congruence in metavariable arguments
  𝑚≈₁ : {𝔪₁ 𝔪₂ : Π ⊩ α ∈ 𝔐}{σ : Π ~[ 𝓐 𝔐 ]↝ Γ}
      → 𝔪₁ ≡ 𝔪₂
      → 𝑚𝑣𝑎𝑟 𝔪₁ σ ≡ 𝑚𝑣𝑎𝑟 𝔪₂ σ
  𝑚≈₁ refl = refl

  𝑚≈₂ : {𝔪 : Π ⊩ α ∈ 𝔐}{σ ς : Π ~[ 𝓐 𝔐 ]↝ Γ}
      → ({τ : T}(v : ℐ τ Π) → σ v ≡ ς v)
      → 𝑚𝑣𝑎𝑟 𝔪 σ ≡ 𝑚𝑣𝑎𝑟 𝔪 ς
  𝑚≈₂ {𝔪 = 𝔪} p = cong (𝑚𝑣𝑎𝑟 𝔪) (dext p)

-- Meta-algebra homomorphism
record MetaAlg⇒ {𝓐 𝓑 : Family₂}(𝓐ᵃ : MetaAlg 𝓐)(𝓑ᵃ : MetaAlg 𝓑)
                (f : 𝓐 ⇾̣₂ 𝓑) : Set where
  private module 𝓐 = MetaAlg 𝓐ᵃ
  private module 𝓑 = MetaAlg 𝓑ᵃ

  field
    ⟨𝑎𝑙𝑔⟩  : {t : ⅀ (𝓐 𝔐) α Γ} → f (𝓐.𝑎𝑙𝑔 t) ≡ 𝓑.𝑎𝑙𝑔 (⅀₁ f t)
    ⟨𝑣𝑎𝑟⟩  : {v : ℐ α Γ} → f (𝓐.𝑣𝑎𝑟 {𝔐} v) ≡ 𝓑.𝑣𝑎𝑟 v
    ⟨𝑚𝑣𝑎𝑟⟩ : {𝔪 : Π ⊩ α ∈ 𝔐}{ε : Π ~[ 𝓐 𝔐 ]↝ Γ} → f (𝓐.𝑚𝑣𝑎𝑟 𝔪 ε) ≡ 𝓑.𝑚𝑣𝑎𝑟 𝔪 (f ∘ ε)
    ⟨𝑏𝑜𝑥⟩ : {b : B (𝓐 𝔐) α Γ} → f (𝓐.𝑏𝑜𝑥 {Γ = Γ} b) ≡ 𝓑.𝑏𝑜𝑥 (B₁ f {α}{Γ} b) --(proj₁ b , proj₁ (proj₂ b) , proj₁ (proj₂ (proj₂ b)) , f (proj₂ (proj₂ (proj₂ b))))
    ⟨𝑙𝑒𝑡𝑏𝑜𝑥⟩ : {lb : LB 𝓐 𝔐 α Γ} → f (𝓐.𝑙𝑒𝑡𝑏𝑜𝑥 lb) ≡ 𝓑.𝑙𝑒𝑡𝑏𝑜𝑥 (proj₁ lb , proj₁ (proj₂ lb) , f (proj₁ (proj₂ (proj₂ lb))) , f (proj₂ (proj₂ (proj₂ lb))))

    -- Really just B₁ and LB₁ but that's not working due to implicit argument shenanigans

-- Category of meta-algebras
module MetaAlgebraStructure = Structure 𝔽amilies₂ MetaAlg

MetaAlgebraCatProps : MetaAlgebraStructure.CategoryProps
MetaAlgebraCatProps = record
  { IsHomomorphism = MetaAlg⇒
  ; id-hom = λ {𝓐}{𝓐ᵃ} → record
    { ⟨𝑎𝑙𝑔⟩ = cong (𝑎𝑙𝑔 𝓐ᵃ) (sym ⅀.identity)
    ; ⟨𝑣𝑎𝑟⟩ = refl
    ; ⟨𝑚𝑣𝑎𝑟⟩ = refl
    ; ⟨𝑏𝑜𝑥⟩ = refl
    ; ⟨𝑙𝑒𝑡𝑏𝑜𝑥⟩ = refl
    }
  ; comp-hom = λ{ {𝐶ˢ = 𝓐ᵃ}{𝓑ᵃ}{𝓒ᵃ} g f gᵃ⇒ fᵃ⇒ → record
    { ⟨𝑎𝑙𝑔⟩ = trans (cong g (⟨𝑎𝑙𝑔⟩ fᵃ⇒))
            (trans (⟨𝑎𝑙𝑔⟩  gᵃ⇒)
                    (cong (𝑎𝑙𝑔 𝓒ᵃ) (sym ⅀.homomorphism)))
    ; ⟨𝑣𝑎𝑟⟩ = trans (cong g (⟨𝑣𝑎𝑟⟩ fᵃ⇒)) (⟨𝑣𝑎𝑟⟩ gᵃ⇒)
    ; ⟨𝑚𝑣𝑎𝑟⟩ = trans (cong g (⟨𝑚𝑣𝑎𝑟⟩ fᵃ⇒)) (⟨𝑚𝑣𝑎𝑟⟩ gᵃ⇒)
    ; ⟨𝑏𝑜𝑥⟩ = trans (cong g (⟨𝑏𝑜𝑥⟩ fᵃ⇒)) (⟨𝑏𝑜𝑥⟩ gᵃ⇒)
    ; ⟨𝑙𝑒𝑡𝑏𝑜𝑥⟩ = trans (cong g (⟨𝑙𝑒𝑡𝑏𝑜𝑥⟩ fᵃ⇒)) (⟨𝑙𝑒𝑡𝑏𝑜𝑥⟩ gᵃ⇒)
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
idᵃ : {𝓐 : Family₂} → (𝓐ᵃ : MetaAlg 𝓐) → MetaAlg⇒ 𝓐ᵃ 𝓐ᵃ id
idᵃ 𝓐ᵃ = record
  { ⟨𝑎𝑙𝑔⟩ = cong (MetaAlg.𝑎𝑙𝑔 𝓐ᵃ) (sym ⅀.identity)
  ; ⟨𝑣𝑎𝑟⟩ = refl
  ; ⟨𝑚𝑣𝑎𝑟⟩ = refl
  ; ⟨𝑏𝑜𝑥⟩ = refl
  ; ⟨𝑙𝑒𝑡𝑏𝑜𝑥⟩ = refl
  }
