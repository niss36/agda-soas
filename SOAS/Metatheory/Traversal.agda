
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
  (𝔛 : Familyₛ) (open SOAS.Metatheory.MetaAlgebra ⅀F 𝔛 [_]_)
  (𝕋:Init : Initial 𝕄etaAlgebras)
  where

open import SOAS.Variable
open import SOAS.Abstract.Hom
import SOAS.Abstract.Coalgebra as →□ ; open →□.Sorted
import SOAS.Abstract.Box as □ ; open □.Sorted

open import SOAS.Metatheory.Algebra ⅀F
open import SOAS.Metatheory.Semantics [_]_ ⅀F ⅀:Str 𝔛 𝕋:Init

open Strength ⅀:Str

private
  variable
    Γ Δ Θ Π Ψ : Ctx
    α β : T
    𝒫 𝒬 𝒜 : Familyₛ


-- Parametrised interpretation into an internal hom
module Traversal (𝒫ᴮ : Coalgₚ 𝒫)(𝑎𝑙𝑔 : ⅀ 𝒜 ⇾̣ 𝒜)
                 (φ : 𝒫 ⇾̣ 𝒜)(χ : 𝔛 ⇾̣ 〖 𝒜 , 𝒜 〗)(𝑏𝑜𝑥 : {Ψ : Ctx} → K₀ Ψ 𝒜 ⇾̣ δ₀ Ψ 𝒜) where
  open Coalgₚ 𝒫ᴮ

  -- Under the assumptions 𝒜 and 〖 𝒫 , 𝒜 〗 are both meta-algebras
  𝒜ᵃ : MetaAlg 𝒜
  𝒜ᵃ = record { 𝑎𝑙𝑔 = 𝑎𝑙𝑔 ; 𝑣𝑎𝑟 = λ x → φ (η x) ; 𝑚𝑣𝑎𝑟 = χ ; 𝑏𝑜𝑥 = 𝑏𝑜𝑥 }

  Travᵃ : MetaAlg 〖 𝒫 , 𝒜 〗
  Travᵃ = record
    { 𝑎𝑙𝑔  = λ t σ → 𝑎𝑙𝑔 (str 𝒫ᴮ 𝒜 t σ)
    ; 𝑣𝑎𝑟  = λ x σ → φ (σ x)
    ; 𝑚𝑣𝑎𝑟 = λ 𝔪 ε σ → χ 𝔪 (λ 𝔫 → ε 𝔫 σ)
    ; 𝑏𝑜𝑥 = λ t σ → 𝑏𝑜𝑥 (t η)
    }

  -- 〖 𝒫 , 𝒜 〗 is also a pointed □-coalgebra
  Travᵇ : Coalg 〖 𝒫 , 𝒜 〗
  Travᵇ = record { r = λ h ρ σ → h (σ ∘ ρ) ; counit = refl ; comult = refl }

  Travᴮ : Coalgₚ 〖 𝒫 , 𝒜 〗
  Travᴮ = record { ᵇ = Travᵇ ; η = λ x σ → φ (σ x) ; r∘η = refl }

  open Semantics Travᵃ public renaming (𝕤𝕖𝕞 to 𝕥𝕣𝕒𝕧)

  -- Traversal-specific homomorphism properties that incorporate a substitution
  𝕥⟨𝕧⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{x : ℐ α Γ} → 𝕥𝕣𝕒𝕧 (𝕧𝕒𝕣 x) σ ≡ φ (σ x)
  𝕥⟨𝕧⟩ {σ = σ} = cong (λ - → - σ) ⟨𝕧⟩

  𝕥⟨𝕞⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{𝔪 : 𝔛 α Π}{ε : Π ~[ 𝕋 ]↝ Γ}
       → 𝕥𝕣𝕒𝕧 (𝕞𝕧𝕒𝕣 𝔪 ε) σ ≡ χ 𝔪 (λ p → 𝕥𝕣𝕒𝕧 (ε p) σ)
  𝕥⟨𝕞⟩ {σ = σ} = cong (λ - → - σ) ⟨𝕞⟩

  𝕥⟨𝕒⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{t : ⅀ 𝕋 α Γ}
       → 𝕥𝕣𝕒𝕧 (𝕒𝕝𝕘 t) σ ≡ 𝑎𝑙𝑔 (str 𝒫ᴮ 𝒜 (⅀₁ 𝕥𝕣𝕒𝕧 t) σ)
  𝕥⟨𝕒⟩ {σ = σ} = cong (λ - → - σ) ⟨𝕒⟩

  𝕥⟨𝕓⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{b : K₀ Ψ 𝕋 α Γ}
        → 𝕥𝕣𝕒𝕧 (𝕓𝕠𝕩 b) σ ≡ 𝑏𝑜𝑥 (𝕥𝕣𝕒𝕧 b η)
  𝕥⟨𝕓⟩ {σ = σ} = cong (λ - → - σ) ⟨𝕓⟩

  -- Congruence in the two arguments of 𝕥𝕣𝕒𝕧
  𝕥≈₁ : {σ : Γ ~[ 𝒫 ]↝ Δ}{t₁ t₂ : 𝕋 α Γ} → t₁ ≡ t₂ → 𝕥𝕣𝕒𝕧 t₁ σ ≡ 𝕥𝕣𝕒𝕧 t₂ σ
  𝕥≈₁ {σ = σ} p = cong (λ - → 𝕥𝕣𝕒𝕧 - σ) p

  𝕥≈₂ : {σ₁ σ₂ : Γ ~[ 𝒫 ]↝ Δ}{t : 𝕋 α Γ}
      → ({τ : T}{x : ℐ τ Γ} → σ₁ x ≡ σ₂ x)
      → 𝕥𝕣𝕒𝕧 t σ₁ ≡ 𝕥𝕣𝕒𝕧 t σ₂
  𝕥≈₂ {t = t} p = cong (𝕥𝕣𝕒𝕧 t) (dext′ p)


-- A pointed meta-Λ-algebra induces 𝕒𝕝𝕘 traversal into □ 𝒜
module □Traversal {𝒜} (𝒜ᵃ : MetaAlg 𝒜) =
  Traversal ℐᴮ (MetaAlg.𝑎𝑙𝑔 𝒜ᵃ) (MetaAlg.𝑣𝑎𝑟 𝒜ᵃ) (MetaAlg.𝑚𝑣𝑎𝑟 𝒜ᵃ) (MetaAlg.𝑏𝑜𝑥 𝒜ᵃ)

-- Corollary: □ lifts to an endofunctor on pointed meta-Λ-algebras
□ᵃ : (𝒜ᵃ : MetaAlg 𝒜) → MetaAlg (□ 𝒜)
□ᵃ = □Traversal.Travᵃ

-- Helper records for proving equality of maps f, g out of 𝕋,
-- with 0, 1 or 2 parameters
record MapEq₀ (𝒜 : Familyₛ)(f g : 𝕋 ⇾̣ 𝒜) : Set where
  field
    ᵃ : MetaAlg 𝒜
  open Semantics ᵃ
  open 𝒜

  field
    f⟨𝑣⟩ : {x : ℐ α Γ}
         → f (𝕧𝕒𝕣 x) ≡ 𝑣𝑎𝑟 x
    f⟨𝑚⟩ : {𝔪 : 𝔛 α Π}{ε : Π ~[ 𝕋 ]↝ Γ}
         → f (𝕞𝕧𝕒𝕣 𝔪 ε) ≡ 𝑚𝑣𝑎𝑟 𝔪 (f ∘ ε)
    f⟨𝑎⟩ : {t : ⅀ 𝕋 α Γ}
         → f (𝕒𝕝𝕘 t) ≡ 𝑎𝑙𝑔 (⅀₁ f t)
    f⟨𝑏⟩ : {b : K₀ Ψ 𝕋 α Γ}
         → f (𝕓𝕠𝕩 b) ≡ 𝑏𝑜𝑥 {Γ = Γ} (f b)
    g⟨𝑣⟩ : {x : ℐ α Γ}
         → g (𝕧𝕒𝕣 x) ≡ 𝑣𝑎𝑟 x
    g⟨𝑚⟩ : {𝔪 : 𝔛 α Π}{ε : Π ~[ 𝕋 ]↝ Γ}
         → g (𝕞𝕧𝕒𝕣 𝔪 ε) ≡ 𝑚𝑣𝑎𝑟 𝔪 (g ∘ ε)
    g⟨𝑎⟩ : {t : ⅀ 𝕋 α Γ}
         → g (𝕒𝕝𝕘 t) ≡ 𝑎𝑙𝑔 (⅀₁ g t)
    g⟨𝑏⟩ : {b : K₀ Ψ 𝕋 α Γ}
         → g (𝕓𝕠𝕩 b) ≡ 𝑏𝑜𝑥 {Γ = Γ} (g b)

  fᵃ : MetaAlg⇒ 𝕋ᵃ ᵃ f
  fᵃ = record { ⟨𝑎𝑙𝑔⟩ =  f⟨𝑎⟩ ; ⟨𝑣𝑎𝑟⟩ =  f⟨𝑣⟩ ; ⟨𝑚𝑣𝑎𝑟⟩ =  f⟨𝑚⟩ ; ⟨𝑏𝑜𝑥⟩ = f⟨𝑏⟩ }
  gᵃ : MetaAlg⇒ 𝕋ᵃ ᵃ g
  gᵃ = record { ⟨𝑎𝑙𝑔⟩ =  g⟨𝑎⟩ ; ⟨𝑣𝑎𝑟⟩ =  g⟨𝑣⟩ ; ⟨𝑚𝑣𝑎𝑟⟩ =  g⟨𝑚⟩ ; ⟨𝑏𝑜𝑥⟩ = g⟨𝑏⟩ }

  ≈ : (t : 𝕋 α Γ) → f t ≡ g t
  ≈ t = eq fᵃ gᵃ t

record MapEq₁ (𝒫ᴮ : Coalgₚ 𝒫)(𝑎𝑙𝑔 : ⅀ 𝒜 ⇾̣ 𝒜)
              (f g : 𝕋 ⇾̣ 〖 𝒫 , 𝒜 〗)(𝑏𝑜𝑥 : {Ψ : Ctx} → K₀ Ψ 𝒜 ⇾̣ δ₀ Ψ 𝒜) : Set where
  field
    φ : 𝒫 ⇾̣ 𝒜
    χ : 𝔛 ⇾̣ 〖 𝒜 , 𝒜 〗

  open Traversal 𝒫ᴮ 𝑎𝑙𝑔 φ χ 𝑏𝑜𝑥

  open Coalgₚ 𝒫ᴮ

  field
    f⟨𝑣⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{x : ℐ α Γ}
         → f (𝕧𝕒𝕣 x) σ ≡ φ (σ x)
    f⟨𝑚⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{𝔪 : 𝔛 α Π}{ε : Π ~[ 𝕋 ]↝ Γ}
         → f (𝕞𝕧𝕒𝕣 𝔪 ε) σ ≡ χ 𝔪 (λ p → f (ε p) σ)
    f⟨𝑎⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{t : ⅀ 𝕋 α Γ}
         → f (𝕒𝕝𝕘 t) σ ≡ 𝑎𝑙𝑔 (str 𝒫ᴮ 𝒜 (⅀₁ f t) σ)
    f⟨𝑏⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{b : K₀ Ψ 𝕋 α Γ}
         → f (𝕓𝕠𝕩 b) σ ≡ 𝑏𝑜𝑥 (f b η)
    g⟨𝑣⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{x : ℐ α Γ}
         → g (𝕧𝕒𝕣 x) σ ≡ φ (σ x)
    g⟨𝑚⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{𝔪 : 𝔛 α Π}{ε : Π ~[ 𝕋 ]↝ Γ}
         → g (𝕞𝕧𝕒𝕣 𝔪 ε) σ ≡ χ 𝔪 (λ p → g (ε p) σ)
    g⟨𝑎⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{t : ⅀ 𝕋 α Γ}
         → g (𝕒𝕝𝕘 t) σ ≡ 𝑎𝑙𝑔 (str 𝒫ᴮ 𝒜 (⅀₁ g t) σ)
    g⟨𝑏⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{b : K₀ Ψ 𝕋 α Γ}
         → g (𝕓𝕠𝕩 b) σ ≡ 𝑏𝑜𝑥 (g b η)

  fᵃ : MetaAlg⇒ 𝕋ᵃ Travᵃ f
  fᵃ = record { ⟨𝑎𝑙𝑔⟩ = dext′ f⟨𝑎⟩ ; ⟨𝑣𝑎𝑟⟩ = dext′ f⟨𝑣⟩ ; ⟨𝑚𝑣𝑎𝑟⟩ = dext′ f⟨𝑚⟩ ; ⟨𝑏𝑜𝑥⟩ = dext′ f⟨𝑏⟩ }
  gᵃ : MetaAlg⇒ 𝕋ᵃ Travᵃ g
  gᵃ = record { ⟨𝑎𝑙𝑔⟩ = dext′ g⟨𝑎⟩ ; ⟨𝑣𝑎𝑟⟩ = dext′ g⟨𝑣⟩ ; ⟨𝑚𝑣𝑎𝑟⟩ = dext′ g⟨𝑚⟩ ; ⟨𝑏𝑜𝑥⟩ = dext′ g⟨𝑏⟩ }

  ≈ : {σ : Γ ~[ 𝒫 ]↝ Δ}(t : 𝕋 α Γ) → f t σ ≡ g t σ
  ≈ {σ = σ} t = cong (λ - → - σ) (eq fᵃ gᵃ t)

record MapEq₂ (𝒫ᴮ : Coalgₚ 𝒫)(𝒬ᴮ : Coalgₚ 𝒬)(𝑎𝑙𝑔 : ⅀ 𝒜 ⇾̣ 𝒜)
                (f g : 𝕋 ⇾̣ 〖 𝒫 , 〖 𝒬 , 𝒜 〗 〗)(𝑏𝑜𝑥 : {Ψ : Ctx} → K₀ Ψ 𝒜 ⇾̣ δ₀ Ψ 𝒜) : Set where
  field
    φ : 𝒬 ⇾̣ 𝒜
    ϕ : 𝒫 ⇾̣ 〖 𝒬 , 𝒜 〗
    χ : 𝔛 ⇾̣ 〖 𝒜 , 𝒜 〗

  open Coalgₚ 𝒫ᴮ renaming (η to 𝒫η)
  open Coalgₚ 𝒬ᴮ renaming (η to 𝒬η)

  open Traversal 𝒫ᴮ (Traversal.𝒜.𝑎𝑙𝑔 𝒬ᴮ 𝑎𝑙𝑔 φ χ 𝑏𝑜𝑥) ϕ (λ 𝔪 ε σ → χ 𝔪 (λ 𝔫 → ε 𝔫 σ)) (λ {Ψ : Ctx} b σ → 𝑏𝑜𝑥 (b 𝒬η))

  field
    f⟨𝑣⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{ς : Δ ~[ 𝒬 ]↝ Θ}{x : ℐ α Γ}
         → f (𝕧𝕒𝕣 x) σ ς ≡ ϕ (σ x) ς
    f⟨𝑚⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{ς : Δ ~[ 𝒬 ]↝ Θ}{𝔪 : 𝔛 α Π}{ε : Π ~[ 𝕋 ]↝ Γ}
         → f (𝕞𝕧𝕒𝕣 𝔪 ε) σ ς ≡ χ 𝔪 (λ 𝔫 → f (ε 𝔫) σ ς)
    f⟨𝑎⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{ς : Δ ~[ 𝒬 ]↝ Θ}{t : ⅀ 𝕋 α Γ}
         → f (𝕒𝕝𝕘 t) σ ς ≡ 𝑎𝑙𝑔 (str 𝒬ᴮ 𝒜 (str 𝒫ᴮ 〖 𝒬 , 𝒜 〗 (⅀₁ f t) σ) ς)
    f⟨𝑏⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{ς : Δ ~[ 𝒬 ]↝ Θ}{b : K₀ Ψ 𝕋 α Γ}
         → f (𝕓𝕠𝕩 b) σ ς ≡ 𝑏𝑜𝑥 (f b 𝒫η 𝒬η)
    g⟨𝑣⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{ς : Δ ~[ 𝒬 ]↝ Θ}{x : ℐ α Γ}
         → g (𝕧𝕒𝕣 x) σ ς ≡ ϕ (σ x) ς
    g⟨𝑚⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{ς : Δ ~[ 𝒬 ]↝ Θ}{𝔪 : 𝔛 α Π}{ε : Π ~[ 𝕋 ]↝ Γ}
         → g (𝕞𝕧𝕒𝕣 𝔪 ε) σ ς ≡ χ 𝔪 (λ 𝔫 → g (ε 𝔫) σ ς)
    g⟨𝑎⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{ς : Δ ~[ 𝒬 ]↝ Θ}{t : ⅀ 𝕋 α Γ}
         → g (𝕒𝕝𝕘 t) σ ς ≡ 𝑎𝑙𝑔 (str 𝒬ᴮ 𝒜 (str 𝒫ᴮ 〖 𝒬 , 𝒜 〗 (⅀₁ g t) σ) ς)
    g⟨𝑏⟩ : {σ : Γ ~[ 𝒫 ]↝ Δ}{ς : Δ ~[ 𝒬 ]↝ Θ}{b : K₀ Ψ 𝕋 α Γ}
         → g (𝕓𝕠𝕩 b) σ ς ≡ 𝑏𝑜𝑥 (g b 𝒫η 𝒬η)

  fᵃ : MetaAlg⇒ 𝕋ᵃ Travᵃ f
  fᵃ = record { ⟨𝑎𝑙𝑔⟩ = dext′ (dext′ f⟨𝑎⟩) ; ⟨𝑣𝑎𝑟⟩ = dext′ (dext′ f⟨𝑣⟩)
              ; ⟨𝑚𝑣𝑎𝑟⟩ = dext′ (dext′ f⟨𝑚⟩) ; ⟨𝑏𝑜𝑥⟩ = dext′ (dext′ f⟨𝑏⟩) }
  gᵃ : MetaAlg⇒ 𝕋ᵃ Travᵃ g
  gᵃ = record { ⟨𝑎𝑙𝑔⟩ = dext′ (dext′ g⟨𝑎⟩) ; ⟨𝑣𝑎𝑟⟩ = dext′ (dext′ g⟨𝑣⟩)
              ; ⟨𝑚𝑣𝑎𝑟⟩ = dext′ (dext′ g⟨𝑚⟩) ; ⟨𝑏𝑜𝑥⟩ = dext′ (dext′ g⟨𝑏⟩) }

  ≈ : {σ : Γ ~[ 𝒫 ]↝ Δ}{ς : Δ ~[ 𝒬 ]↝ Θ}(t : 𝕋 α Γ) → f t σ ς ≡ g t σ ς
  ≈ {σ = σ}{ς} t = cong (λ - → - σ ς) (eq fᵃ gᵃ t)

-- Interaction of traversal and interpretation
module _ (𝒫ᴮ : Coalgₚ 𝒫)(𝒜ᵃ : MetaAlg 𝒜)(φ : 𝒫 ⇾̣ 𝒜) where
  open MetaAlg 𝒜ᵃ
  open Coalgₚ 𝒫ᴮ
  open Semantics 𝒜ᵃ
  open Traversal 𝒫ᴮ 𝑎𝑙𝑔 φ 𝑚𝑣𝑎𝑟 𝑏𝑜𝑥 using (𝕥𝕣𝕒𝕧 ; 𝕥⟨𝕒⟩ ; 𝕥⟨𝕧⟩ ; 𝕥⟨𝕞⟩; 𝕥⟨𝕓⟩)
  open ≡-Reasoning

  -- Traversal with the point of 𝒫 is the same as direct interpretation
  𝕥𝕣𝕒𝕧-η≈𝕤𝕖𝕞 : (φ∘η≈𝑣𝑎𝑟 : ∀{α Γ}{v : ℐ α Γ} → φ (η v) ≡ 𝑣𝑎𝑟 v){t : 𝕋 α Γ}
        → 𝕥𝕣𝕒𝕧 t η ≡ 𝕤𝕖𝕞 t
  𝕥𝕣𝕒𝕧-η≈𝕤𝕖𝕞 φ∘η≈𝑣𝑎𝑟 {t = t} = Semantics.eq 𝒜ᵃ (record
    { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → trans 𝕥⟨𝕒⟩ (cong 𝑎𝑙𝑔 (begin
          str 𝒫ᴮ 𝒜 (⅀₁ 𝕥𝕣𝕒𝕧 t) η
      ≡⟨ str-nat₁ (ηᴮ⇒ 𝒫ᴮ) (⅀₁ 𝕥𝕣𝕒𝕧 t) id ⟩
          str ℐᴮ 𝒜 (⅀₁ (λ{ h ρ → h (η ∘ ρ)}) ((⅀₁ 𝕥𝕣𝕒𝕧 t))) id
      ≡⟨ str-unit 𝒜 ((⅀₁ (λ{ h ρ → h (η ∘ ρ)}) ((⅀₁ 𝕥𝕣𝕒𝕧 t)))) ⟩
          ⅀₁ (i 𝒜) (⅀₁ (λ { h ρ → h (η ∘ ρ) }) (⅀₁ 𝕥𝕣𝕒𝕧 t))
      ≡˘⟨ trans ⅀.homomorphism ⅀.homomorphism ⟩
          ⅀₁ (λ t → 𝕥𝕣𝕒𝕧 t η) t
      ∎))}
    ; ⟨𝑣𝑎𝑟⟩ = λ{ {v = v} → trans 𝕥⟨𝕧⟩ φ∘η≈𝑣𝑎𝑟 }
    ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪}{ε} → 𝕥⟨𝕞⟩ }
    ; ⟨𝑏𝑜𝑥⟩ = 𝕥⟨𝕓⟩ }) 𝕤𝕖𝕞ᵃ⇒ t

-- Traversal with the point of 𝒫 into 𝕋  is the identity
𝕥𝕣𝕒𝕧-η≈id : (𝒫ᴮ : Coalgₚ 𝒫)(open Coalgₚ 𝒫ᴮ)(φ : 𝒫 ⇾̣ 𝕋)
          (φ∘η≈𝑣𝑎𝑟 : ∀{α Γ}{v : ℐ α Γ} → φ (η v) ≡ 𝕧𝕒𝕣 v){t : 𝕋 α Γ}
         → Traversal.𝕥𝕣𝕒𝕧 𝒫ᴮ 𝕒𝕝𝕘 φ 𝕞𝕧𝕒𝕣 𝕓𝕠𝕩 t η ≡ t
𝕥𝕣𝕒𝕧-η≈id 𝒫ᴮ φ φ∘η≈𝑣𝑎𝑟 = trans (𝕥𝕣𝕒𝕧-η≈𝕤𝕖𝕞 𝒫ᴮ 𝕋ᵃ φ φ∘η≈𝑣𝑎𝑟) 𝕤𝕖𝕞-id

-- Corollaries for ℐ-parametrised traversals
□𝕥𝕣𝕒𝕧-id≈𝕤𝕖𝕞 : (𝒜ᵃ : MetaAlg 𝒜){t : 𝕋 α Γ}
            → □Traversal.𝕥𝕣𝕒𝕧 𝒜ᵃ t id ≡ Semantics.𝕤𝕖𝕞 𝒜ᵃ t
□𝕥𝕣𝕒𝕧-id≈𝕤𝕖𝕞 𝒜ᵃ {t} = 𝕥𝕣𝕒𝕧-η≈𝕤𝕖𝕞 ℐᴮ 𝒜ᵃ (MetaAlg.𝑣𝑎𝑟 𝒜ᵃ) refl

□𝕥𝕣𝕒𝕧-id≈id : {t : 𝕋 α Γ} → □Traversal.𝕥𝕣𝕒𝕧 𝕋ᵃ t id ≡ t
□𝕥𝕣𝕒𝕧-id≈id = 𝕥𝕣𝕒𝕧-η≈id ℐᴮ 𝕧𝕒𝕣 refl
