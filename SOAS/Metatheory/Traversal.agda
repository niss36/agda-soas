
open import SOAS.Common
open import SOAS.Families.Core
open import Categories.Object.Initial
open import SOAS.Coalgebraic.Strength
import SOAS.Metatheory.MetaAlgebra
import SOAS.Context

-- Traversals parametrised by a pointed coalgebra
module SOAS.Metatheory.Traversal {T : Set}
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

open import SOAS.Metatheory.Algebra ⅀F
open import SOAS.Metatheory.Contextual [_]_
open import SOAS.Metatheory.Semantics [_]_ ⅀F ⅀:Str 𝕋:Init

open Strength ⅀:Str

private
  variable
    Γ Δ Θ Π Ψ : Ctx
    α β : T
    𝓟 𝓠 𝓐 : Family₂


-- Parametrised interpretation into an internal hom
module Traversal (𝓟ᴮ : {𝔐 : MCtx} → Coalgₚ (𝓟 𝔐))
                 (𝑎𝑙𝑔 : (⅀ ²) 𝓐 ⇾̣₂ 𝓐)
                 (φ : 𝓟 ⇾̣₂ 𝓐)
                 (χ : ∥_∥ ⇾̣₂ 〖 𝓐 , 𝓐 〗²)
                 (𝑏𝑜𝑥 : {Ψ : Ctx} → (K Ψ ²) 𝓐 ⇾̣₂ (δbox Ψ ²) 𝓐)
  private
    open module - {𝔐} = Coalgₚ (𝓟ᴮ {𝔐})

  -- Under the assumptions 𝓐 and 〖 𝓟 , 𝓐 〗 are both meta-algebras
  𝓐ᵃ : MetaAlg 𝓐
  𝓐ᵃ = record { 𝑎𝑙𝑔 = 𝑎𝑙𝑔 ; 𝑣𝑎𝑟 = λ x → φ (η x) ; 𝑚𝑣𝑎𝑟 = χ ; 𝑏𝑜𝑥 = 𝑏𝑜𝑥 }

  Travᵃ : MetaAlg 〖 𝓟 , 𝓐 〗²
  Travᵃ = record
    { 𝑎𝑙𝑔  = λ {𝔐} t σ → 𝑎𝑙𝑔 (str 𝓟ᴮ (𝓐 𝔐) t σ)
    ; 𝑣𝑎𝑟  = λ x σ → φ (σ x)
    ; 𝑚𝑣𝑎𝑟 = λ 𝔪 ε σ → χ 𝔪 (λ 𝔫 → ε 𝔫 σ)
    ; 𝑏𝑜𝑥 = λ t σ → 𝑏𝑜𝑥 (t η)
    }

  -- 〖 𝓟 , 𝓐 〗 is also a pointed □-coalgebra
  Travᵇ : {𝔐 : MCtx} → Coalg (〖 𝓟 , 𝓐 〗² 𝔐)
  Travᵇ = record { r = λ h ρ σ → h (σ ∘ ρ) ; counit = refl ; comult = refl }

  Travᴮ : {𝔐 : MCtx} → Coalgₚ (〖 𝓟 , 𝓐 〗² 𝔐)
  Travᴮ = record { ᵇ = Travᵇ ; η = λ x σ → φ (σ x) ; r∘η = refl }

  open Semantics Travᵃ public renaming (𝕤𝕖𝕞 to 𝕥𝕣𝕒𝕧)

  -- Traversal-specific homomorphism properties that incorporate a substitution
  𝕥⟨𝕧⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{x : ℐ α Γ} → 𝕥𝕣𝕒𝕧 (𝕧𝕒𝕣 x) σ ≡ φ (σ x)
  𝕥⟨𝕧⟩ {σ = σ} = cong (λ - → - σ) ⟨𝕧⟩

  𝕥⟨𝕞⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{𝔪 : Π ⊩ α ∈ 𝔐}{ε : Π ~[ 𝕋 𝔐 ]↝ Γ}
       → 𝕥𝕣𝕒𝕧 (𝕞𝕧𝕒𝕣 𝔪 ε) σ ≡ χ 𝔪 (λ p → 𝕥𝕣𝕒𝕧 (ε p) σ)
  𝕥⟨𝕞⟩ {σ = σ} = cong (λ - → - σ) ⟨𝕞⟩

  𝕥⟨𝕒⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{t : ⅀ (𝕋 𝔐) α Γ}
       → 𝕥𝕣𝕒𝕧 (𝕒𝕝𝕘 t) σ ≡ 𝑎𝑙𝑔 (str 𝓟ᴮ (𝓐 𝔐) (⅀₁ 𝕥𝕣𝕒𝕧 t) σ)
  𝕥⟨𝕒⟩ {σ = σ} = cong (λ - → - σ) ⟨𝕒⟩

  𝕥⟨𝕓⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{b : K Ψ (𝕋 𝔐) α Γ}
        → 𝕥𝕣𝕒𝕧 (𝕓𝕠𝕩 b) σ ≡ 𝑏𝑜𝑥 (𝕥𝕣𝕒𝕧 b η)
  𝕥⟨𝕓⟩ {σ = σ} = cong (λ - → - σ) ⟨𝕓⟩

  -- Congruence in the two arguments of 𝕥𝕣𝕒𝕧
  𝕥≈₁ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{t₁ t₂ : 𝕋 𝔐 α Γ} → t₁ ≡ t₂ → 𝕥𝕣𝕒𝕧 t₁ σ ≡ 𝕥𝕣𝕒𝕧 t₂ σ
  𝕥≈₁ {σ = σ} p = cong (λ - → 𝕥𝕣𝕒𝕧 - σ) p

  𝕥≈₂ : {𝔐 : MCtx}{σ₁ σ₂ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{t : 𝕋 𝔐 α Γ}
      → ({τ : T}{x : ℐ τ Γ} → σ₁ x ≡ σ₂ x)
      → 𝕥𝕣𝕒𝕧 t σ₁ ≡ 𝕥𝕣𝕒𝕧 t σ₂
  𝕥≈₂ {t = t} p = cong (𝕥𝕣𝕒𝕧 t) (dext′ p)


-- A pointed meta-Λ-algebra induces 𝕒𝕝𝕘 traversal into □ 𝓐
module □Traversal {𝓐} (𝓐ᵃ : MetaAlg 𝓐) =
  Traversal ℐᴮ (MetaAlg.𝑎𝑙𝑔 𝓐ᵃ) (MetaAlg.𝑣𝑎𝑟 𝓐ᵃ) (MetaAlg.𝑚𝑣𝑎𝑟 𝓐ᵃ) (MetaAlg.𝑏𝑜𝑥 𝓐ᵃ)

-- Corollary: □ lifts to an endofunctor on pointed meta-Λ-algebras
□ᵃ : (𝓐ᵃ : MetaAlg 𝓐) → MetaAlg ((□ ²) 𝓐)
□ᵃ = □Traversal.Travᵃ

-- Helper records for proving equality of maps f, g out of 𝕋,
-- with 0, 1 or 2 parameters
record MapEq₀ (𝓐 : Family₂)(f g : 𝕋 ⇾̣₂ 𝓐) : Set where
  field
    ᵃ : MetaAlg 𝓐
  open Semantics ᵃ
  open 𝓐

  field
    f⟨𝑣⟩ : {𝔐 : MCtx}{x : ℐ α Γ}
         → f (𝕧𝕒𝕣 x) ≡ 𝑣𝑎𝑟 {𝔐} x
    f⟨𝑚⟩ : {𝔐 : MCtx}{𝔪 : Π ⊩ α ∈ 𝔐}{ε : Π ~[ 𝕋 𝔐 ]↝ Γ}
         → f (𝕞𝕧𝕒𝕣 𝔪 ε) ≡ 𝑚𝑣𝑎𝑟 𝔪 (f ∘ ε)
    f⟨𝑎⟩ : {𝔐 : MCtx}{t : ⅀ (𝕋 𝔐) α Γ}
         → f (𝕒𝕝𝕘 t) ≡ 𝑎𝑙𝑔 (⅀₁ f t)
    f⟨𝑏⟩ : {𝔐 : MCtx}{b : K Ψ (𝕋 𝔐) α Γ}
         → f (𝕓𝕠𝕩 b) ≡ 𝑏𝑜𝑥 {Γ = Γ} (f b)
    g⟨𝑣⟩ : {𝔐 : MCtx}{x : ℐ α Γ}
         → g (𝕧𝕒𝕣 x) ≡ 𝑣𝑎𝑟 {𝔐} x
    g⟨𝑚⟩ : {𝔐 : MCtx}{𝔪 : Π ⊩ α ∈ 𝔐}{ε : Π ~[ 𝕋 𝔐 ]↝ Γ}
         → g (𝕞𝕧𝕒𝕣 𝔪 ε) ≡ 𝑚𝑣𝑎𝑟 𝔪 (g ∘ ε)
    g⟨𝑎⟩ : {𝔐 : MCtx}{t : ⅀ (𝕋 𝔐) α Γ}
         → g (𝕒𝕝𝕘 t) ≡ 𝑎𝑙𝑔 (⅀₁ g t)
    g⟨𝑏⟩ : {𝔐 : MCtx}{b : K Ψ (𝕋 𝔐) α Γ}
         → g (𝕓𝕠𝕩 b) ≡ 𝑏𝑜𝑥 {Γ = Γ} (g b)

  fᵃ : MetaAlg⇒ 𝕋ᵃ ᵃ f
  fᵃ = record { ⟨𝑎𝑙𝑔⟩ =  f⟨𝑎⟩ ; ⟨𝑣𝑎𝑟⟩ =  f⟨𝑣⟩ ; ⟨𝑚𝑣𝑎𝑟⟩ =  f⟨𝑚⟩ ; ⟨𝑏𝑜𝑥⟩ = f⟨𝑏⟩ }
  gᵃ : MetaAlg⇒ 𝕋ᵃ ᵃ g
  gᵃ = record { ⟨𝑎𝑙𝑔⟩ =  g⟨𝑎⟩ ; ⟨𝑣𝑎𝑟⟩ =  g⟨𝑣⟩ ; ⟨𝑚𝑣𝑎𝑟⟩ =  g⟨𝑚⟩ ; ⟨𝑏𝑜𝑥⟩ = g⟨𝑏⟩ }

  ≈ : {𝔐 : MCtx}(t : 𝕋 𝔐 α Γ) → f t ≡ g t
  ≈ t = eq fᵃ gᵃ t

record MapEq₁ (𝓟ᴮ : {𝔐 : MCtx} → Coalgₚ (𝓟 𝔐))
              (𝑎𝑙𝑔 : (⅀ ²) 𝓐 ⇾̣₂ 𝓐)
              (𝑏𝑜𝑥 : {Ψ : Ctx} → (K Ψ ²) 𝓐 ⇾̣₂ (δbox Ψ ²) 𝓐)
              (f g : 𝕋 ⇾̣₂ 〖 𝓟 , 𝓐 〗²) : Set where
  field
    φ : 𝓟 ⇾̣₂ 𝓐
    χ : ∥_∥ ⇾̣₂ 〖 𝓐 , 𝓐 〗²

  open Traversal 𝓟ᴮ 𝑎𝑙𝑔 φ χ 𝑏𝑜𝑥

  private
    open module - {𝔐} = Coalgₚ (𝓟ᴮ {𝔐})

  field
    f⟨𝑣⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{x : ℐ α Γ}
         → f (𝕧𝕒𝕣 x) σ ≡ φ (σ x)
    f⟨𝑚⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{𝔪 : Π ⊩ α ∈ 𝔐}{ε : Π ~[ 𝕋 𝔐 ]↝ Γ}
         → f (𝕞𝕧𝕒𝕣 𝔪 ε) σ ≡ χ 𝔪 (λ p → f (ε p) σ)
    f⟨𝑎⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{t : ⅀ (𝕋 𝔐) α Γ}
         → f (𝕒𝕝𝕘 t) σ ≡ 𝑎𝑙𝑔 (str 𝓟ᴮ (𝓐 𝔐) (⅀₁ f t) σ)
    f⟨𝑏⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{b : K Ψ (𝕋 𝔐) α Γ}
         → f (𝕓𝕠𝕩 b) σ ≡ 𝑏𝑜𝑥 (f b η)
    g⟨𝑣⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{x : ℐ α Γ}
         → g (𝕧𝕒𝕣 x) σ ≡ φ (σ x)
    g⟨𝑚⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{𝔪 : Π ⊩ α ∈ 𝔐}{ε : Π ~[ 𝕋 𝔐 ]↝ Γ}
         → g (𝕞𝕧𝕒𝕣 𝔪 ε) σ ≡ χ 𝔪 (λ p → g (ε p) σ)
    g⟨𝑎⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{t : ⅀ (𝕋 𝔐) α Γ}
         → g (𝕒𝕝𝕘 t) σ ≡ 𝑎𝑙𝑔 (str 𝓟ᴮ (𝓐 𝔐) (⅀₁ g t) σ)
    g⟨𝑏⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{b : K Ψ (𝕋 𝔐) α Γ}
         → g (𝕓𝕠𝕩 b) σ ≡ 𝑏𝑜𝑥 (g b η)

  fᵃ : MetaAlg⇒ 𝕋ᵃ Travᵃ f
  fᵃ = record { ⟨𝑎𝑙𝑔⟩ = dext′ f⟨𝑎⟩ ; ⟨𝑣𝑎𝑟⟩ = dext′ f⟨𝑣⟩ ; ⟨𝑚𝑣𝑎𝑟⟩ = dext′ f⟨𝑚⟩ ; ⟨𝑏𝑜𝑥⟩ = dext′ f⟨𝑏⟩ }
  gᵃ : MetaAlg⇒ 𝕋ᵃ Travᵃ g
  gᵃ = record { ⟨𝑎𝑙𝑔⟩ = dext′ g⟨𝑎⟩ ; ⟨𝑣𝑎𝑟⟩ = dext′ g⟨𝑣⟩ ; ⟨𝑚𝑣𝑎𝑟⟩ = dext′ g⟨𝑚⟩ ; ⟨𝑏𝑜𝑥⟩ = dext′ g⟨𝑏⟩ }

  ≈ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}(t : 𝕋 𝔐 α Γ) → f t σ ≡ g t σ
  ≈ {σ = σ} t = cong (λ - → - σ) (eq fᵃ gᵃ t)

record MapEq₂ (𝓟ᴮ : {𝔐 : MCtx} → Coalgₚ (𝓟 𝔐))
              (𝓠ᴮ : {𝔐 : MCtx} → Coalgₚ (𝓠 𝔐))
              (𝑎𝑙𝑔 : (⅀ ²) 𝓐 ⇾̣₂ 𝓐)
              (𝑏𝑜𝑥 : {Ψ : Ctx} → (K Ψ ²) 𝓐 ⇾̣₂ (δbox Ψ ²) 𝓐)
              (f g : 𝕋 ⇾̣₂ 〖 𝓟 , 〖 𝓠 , 𝓐 〗² 〗²) : Set where
  field
    φ : 𝓠 ⇾̣₂ 𝓐
    ϕ : 𝓟 ⇾̣₂ 〖 𝓠 , 𝓐 〗²
    χ : ∥_∥ ⇾̣₂ 〖 𝓐 , 𝓐 〗²

  private
    open module P {𝔐} = Coalgₚ (𝓟ᴮ {𝔐}) renaming (η to 𝓟η)
    open module Q {𝔐} = Coalgₚ (𝓠ᴮ {𝔐}) renaming (η to 𝓠η)

  open Traversal 𝓟ᴮ (Traversal.𝓐.𝑎𝑙𝑔 𝓠ᴮ 𝑎𝑙𝑔 φ χ 𝑏𝑜𝑥) ϕ (λ 𝔪 ε σ → χ 𝔪 (λ 𝔫 → ε 𝔫 σ)) (λ b σ → 𝑏𝑜𝑥 (b 𝓠η))

  field
    f⟨𝑣⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{ς : Δ ~[ 𝓠 𝔐 ]↝ Θ}{x : ℐ α Γ}
         → f (𝕧𝕒𝕣 x) σ ς ≡ ϕ (σ x) ς
    f⟨𝑚⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{ς : Δ ~[ 𝓠 𝔐 ]↝ Θ}{𝔪 : Π ⊩ α ∈ 𝔐}{ε : Π ~[ 𝕋 𝔐 ]↝ Γ}
         → f (𝕞𝕧𝕒𝕣 𝔪 ε) σ ς ≡ χ 𝔪 (λ 𝔫 → f (ε 𝔫) σ ς)
    f⟨𝑎⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{ς : Δ ~[ 𝓠 𝔐 ]↝ Θ}{t : ⅀ (𝕋 𝔐) α Γ}
         → f (𝕒𝕝𝕘 t) σ ς ≡ 𝑎𝑙𝑔 (str 𝓠ᴮ (𝓐 𝔐) (str 𝓟ᴮ (〖 𝓠 , 𝓐 〗² 𝔐) (⅀₁ f t) σ) ς)
    f⟨𝑏⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{ς : Δ ~[ 𝓠 𝔐 ]↝ Θ}{b : K Ψ (𝕋 𝔐) α Γ}
         → f (𝕓𝕠𝕩 b) σ ς ≡ 𝑏𝑜𝑥 (f b 𝓟η 𝓠η)
    g⟨𝑣⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{ς : Δ ~[ 𝓠 𝔐 ]↝ Θ}{x : ℐ α Γ}
         → g (𝕧𝕒𝕣 x) σ ς ≡ ϕ (σ x) ς
    g⟨𝑚⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{ς : Δ ~[ 𝓠 𝔐 ]↝ Θ}{𝔪 : Π ⊩ α ∈ 𝔐}{ε : Π ~[ 𝕋 𝔐 ]↝ Γ}
         → g (𝕞𝕧𝕒𝕣 𝔪 ε) σ ς ≡ χ 𝔪 (λ 𝔫 → g (ε 𝔫) σ ς)
    g⟨𝑎⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{ς : Δ ~[ 𝓠 𝔐 ]↝ Θ}{t : ⅀ (𝕋 𝔐) α Γ}
         → g (𝕒𝕝𝕘 t) σ ς ≡ 𝑎𝑙𝑔 (str 𝓠ᴮ (𝓐 𝔐) (str 𝓟ᴮ (〖 𝓠 , 𝓐 〗² 𝔐) (⅀₁ g t) σ) ς)
    g⟨𝑏⟩ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{ς : Δ ~[ 𝓠 𝔐 ]↝ Θ}{b : K Ψ (𝕋 𝔐) α Γ}
         → g (𝕓𝕠𝕩 b) σ ς ≡ 𝑏𝑜𝑥 (g b 𝓟η 𝓠η)

  fᵃ : MetaAlg⇒ 𝕋ᵃ Travᵃ f
  fᵃ = record { ⟨𝑎𝑙𝑔⟩ = dext′ (dext′ f⟨𝑎⟩) ; ⟨𝑣𝑎𝑟⟩ = dext′ (dext′ f⟨𝑣⟩)
              ; ⟨𝑚𝑣𝑎𝑟⟩ = dext′ (dext′ f⟨𝑚⟩) ; ⟨𝑏𝑜𝑥⟩ = dext′ (dext′ f⟨𝑏⟩) }
  gᵃ : MetaAlg⇒ 𝕋ᵃ Travᵃ g
  gᵃ = record { ⟨𝑎𝑙𝑔⟩ = dext′ (dext′ g⟨𝑎⟩) ; ⟨𝑣𝑎𝑟⟩ = dext′ (dext′ g⟨𝑣⟩)
              ; ⟨𝑚𝑣𝑎𝑟⟩ = dext′ (dext′ g⟨𝑚⟩) ; ⟨𝑏𝑜𝑥⟩ = dext′ (dext′ g⟨𝑏⟩) }

  ≈ : {𝔐 : MCtx}{σ : Γ ~[ 𝓟 𝔐 ]↝ Δ}{ς : Δ ~[ 𝓠 𝔐 ]↝ Θ}(t : 𝕋 𝔐 α Γ) → f t σ ς ≡ g t σ ς
  ≈ {σ = σ}{ς} t = cong (λ - → - σ ς) (eq fᵃ gᵃ t)

-- Interaction of traversal and interpretation
module _ (𝓟ᴮ : {𝔐 : MCtx} → Coalgₚ (𝓟 𝔐))(𝓐ᵃ : MetaAlg 𝓐)(φ : 𝓟 ⇾̣₂ 𝓐) where
  open MetaAlg 𝓐ᵃ
  private
    open module - {𝔐} = Coalgₚ (𝓟ᴮ {𝔐})
  open Semantics 𝓐ᵃ
  open Traversal 𝓟ᴮ 𝑎𝑙𝑔 φ 𝑚𝑣𝑎𝑟 𝑏𝑜𝑥 using (𝕥𝕣𝕒𝕧 ; 𝕥⟨𝕒⟩ ; 𝕥⟨𝕧⟩ ; 𝕥⟨𝕞⟩; 𝕥⟨𝕓⟩)
  open ≡-Reasoning

  -- Traversal with the point of 𝓟 is the same as direct interpretation
  𝕥𝕣𝕒𝕧-η≈𝕤𝕖𝕞 : (φ∘η≈𝑣𝑎𝑟 : ∀{α Γ 𝔐}{v : ℐ α Γ} → φ {𝔐} (η v) ≡ 𝑣𝑎𝑟 v){𝔐 : MCtx}{t : 𝕋 𝔐 α Γ}
        → 𝕥𝕣𝕒𝕧 t η ≡ 𝕤𝕖𝕞 t
  𝕥𝕣𝕒𝕧-η≈𝕤𝕖𝕞 φ∘η≈𝑣𝑎𝑟 {t = t} = Semantics.eq 𝓐ᵃ (record
    { ⟨𝑎𝑙𝑔⟩ = λ{ {𝔐}{t = t} → trans 𝕥⟨𝕒⟩ (cong 𝑎𝑙𝑔 (begin
          str (𝓟ᴮ {𝔐}) (𝓐 𝔐) (⅀₁ 𝕥𝕣𝕒𝕧 t) η
      ≡⟨ str-nat₁ (ηᴮ⇒ (𝓟ᴮ {𝔐})) (⅀₁ 𝕥𝕣𝕒𝕧 t) id ⟩
          str ℐᴮ (𝓐 𝔐) (⅀₁ (λ{ h ρ → h (η ∘ ρ)}) ((⅀₁ 𝕥𝕣𝕒𝕧 t))) id
      ≡⟨ str-unit (𝓐 𝔐) ((⅀₁ (λ{ h ρ → h (η ∘ ρ)}) ((⅀₁ 𝕥𝕣𝕒𝕧 t)))) ⟩
          ⅀₁ (i (𝓐 𝔐)) (⅀₁ (λ { h ρ → h (η ∘ ρ) }) (⅀₁ 𝕥𝕣𝕒𝕧 t))
      ≡˘⟨ trans ⅀.homomorphism ⅀.homomorphism ⟩
          ⅀₁ (λ t → 𝕥𝕣𝕒𝕧 t η) t
      ∎))}
    ; ⟨𝑣𝑎𝑟⟩ = λ{ {v = v} → trans 𝕥⟨𝕧⟩ φ∘η≈𝑣𝑎𝑟 }
    ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪}{ε} → 𝕥⟨𝕞⟩ }
    ; ⟨𝑏𝑜𝑥⟩ = 𝕥⟨𝕓⟩ }) 𝕤𝕖𝕞ᵃ⇒ t

-- Traversal with the point of 𝓟 into 𝕋  is the identity
𝕥𝕣𝕒𝕧-η≈id : (𝓟ᴮ : {𝔐 : MCtx} → Coalgₚ (𝓟 𝔐))(φ : 𝓟 ⇾̣₂ 𝕋)
            (φ∘η≈𝑣𝑎𝑟 : ∀{α Γ 𝔐}{v : ℐ α Γ}(open Coalgₚ (𝓟ᴮ {𝔐})) → φ (η v) ≡ 𝕧𝕒𝕣 v)
            {𝔐 : MCtx}{t : 𝕋 𝔐 α Γ}
            (open Coalgₚ (𝓟ᴮ {𝔐}))
          → Traversal.𝕥𝕣𝕒𝕧 𝓟ᴮ 𝕒𝕝𝕘 φ 𝕞𝕧𝕒𝕣 𝕓𝕠𝕩 t η ≡ t
𝕥𝕣𝕒𝕧-η≈id 𝓟ᴮ φ φ∘η≈𝑣𝑎𝑟 = trans (𝕥𝕣𝕒𝕧-η≈𝕤𝕖𝕞 𝓟ᴮ 𝕋ᵃ φ φ∘η≈𝑣𝑎𝑟) 𝕤𝕖𝕞-id

-- Corollaries for ℐ-parametrised traversals
□𝕥𝕣𝕒𝕧-id≈𝕤𝕖𝕞 : (𝓐ᵃ : MetaAlg 𝓐){𝔐 : MCtx}{t : 𝕋 𝔐 α Γ}
            → □Traversal.𝕥𝕣𝕒𝕧 𝓐ᵃ t id ≡ Semantics.𝕤𝕖𝕞 𝓐ᵃ t
□𝕥𝕣𝕒𝕧-id≈𝕤𝕖𝕞 𝓐ᵃ {t} = 𝕥𝕣𝕒𝕧-η≈𝕤𝕖𝕞 ℐᴮ 𝓐ᵃ (MetaAlg.𝑣𝑎𝑟 𝓐ᵃ) refl

□𝕥𝕣𝕒𝕧-id≈id : {𝔐 : MCtx}{t : 𝕋 𝔐 α Γ} → □Traversal.𝕥𝕣𝕒𝕧 𝕋ᵃ t id ≡ t
□𝕥𝕣𝕒𝕧-id≈id = 𝕥𝕣𝕒𝕧-η≈id ℐᴮ 𝕧𝕒𝕣 refl
