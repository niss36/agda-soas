
-- Category of indexed families
module SOAS.Families.Core {T : Set} where

open import SOAS.Common
open import SOAS.Context {T}
open import SOAS.Sorting

open import Categories.Category.Construction.Functors

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

open import Function
open import Relation.Binary using (IsEquivalence)

module Inv where
  open import Function.Properties.Inverse
  open IsEquivalence {1ℓ} ↔-isEquivalence public

foo : {A B : Set} → (f g : A ↔ B) → ((x : A) → (Inverse.f f) x ≡ (Inverse.f g) x) → ((y : B) → (Inverse.f⁻¹ f) y ≡ (Inverse.f⁻¹ g) y)
foo {A} f g eq y = let
    aux : (x : A) → (Inverse.f⁻¹ g) ((Inverse.f f) x) ≡ x
    aux x = trans (cong (Inverse.f⁻¹ g) (eq x)) (Inverse.inverseʳ g x)
  in trans (sym (aux ((Inverse.f⁻¹ f) y))) (cong (Inverse.f⁻¹ g) (Inverse.inverseˡ f y))


𝕄Ctx : Category 0ℓ 0ℓ 0ℓ
𝕄Ctx = categoryHelper record
  { Obj = MCtx
  ; _⇒_ = λ 𝔐 𝔑 → ∀{Π : Ctx}{τ : T} → (Π ⊩ τ ∈ 𝔐) ↔ (Π ⊩ τ ∈ 𝔑) --(Π ⊩ τ ∈ 𝔐) → (Π ⊩ τ ∈ 𝔑)
  ; _≈_ = λ {𝔐}{𝔑} f g → ∀{Π : Ctx}{τ : T}{𝔪 : Π ⊩ τ ∈ 𝔐} → (Inverse.f f) 𝔪 ≡ (Inverse.f g) 𝔪 --(Bijection.to f) ⟨$⟩ 𝔪 ≡ (Bijection.to g) ⟨$⟩ 𝔪 --f 𝔪 ≡ g 𝔪
  ; id = Inv.refl --idBij --id
  ; _∘_ = λ g f {Π}{τ} → Inv.trans f g --λ g f {Π}{τ} → g ∘Bij f -- g ∘ f
  ; assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; equiv = record { refl = refl ; sym = λ p → sym p ; trans = λ p q → trans p q }
  ; ∘-resp-≈ = λ { {f = f} p q → trans (cong (Inverse.f f) q) p } --λ{ {f = f} p q → trans (congEq (Bijection.to f) q) p } --(λ { {f = f} p q → trans (cong f q) p })
  }

import Categories.Category.Equivalence as Equiv

module MCtxEquivOp where

  open Category 𝕄Ctx

  𝕄Ctx-equiv-op : Equiv.StrongEquivalence 𝕄Ctx op
  𝕄Ctx-equiv-op = record
    { F = record
      { F₀ = λ x → x
      ; F₁ = λ {A}{B} f → Inv.sym f
      ; identity = refl
      ; homomorphism = refl
      ; F-resp-≈ = λ{ {f = f}{g = g} x {𝔪 = 𝔫} → foo f g (λ 𝔪 → x) 𝔫 } --λ x → cong (proj₁ ∘′ proj₂) {! x  !}
      }
    ; G = record
      { F₀ = λ x → x
      ; F₁ = λ f → Inv.sym f
      ; identity = refl
      ; homomorphism = refl
      ; F-resp-≈ = λ{ {f = f}{g = g} x {𝔪 = 𝔫} → foo f g (λ 𝔪 → x) 𝔫 }
      }
    ; weak-inverse = record
      { F∘G≈id = record
        { F⇒G = ntHelper record { η = λ X → Inv.refl ; commute = λ f → Inverse.cong₁ f refl }
        ; F⇐G = ntHelper record { η = λ X → Inv.refl ; commute = λ f → Inverse.cong₁ f refl }
        ; iso = λ X → record { isoˡ = refl ; isoʳ = refl }
        }
      ; G∘F≈id = record
        { F⇒G = ntHelper record { η = λ X → Inv.refl ; commute = λ f → Inverse.cong₁ f refl }
        ; F⇐G = ntHelper record { η = λ X → Inv.refl ; commute = λ f → Inverse.cong₁ f refl }
        ; iso = λ X → record { isoˡ = refl ; isoʳ = refl }
        }
      }
    }

-- | Sorted with metavariable context
𝔽amilies₂ : Category 1ℓ 0ℓ 0ℓ
𝔽amilies₂ = Functors 𝕄Ctx 𝔽amiliesₛ
module 𝔽am₂ = Category 𝔽amilies₂

Family₂ : Set₁
Family₂ = 𝔽am₂.Obj

-- Maps between sorted families
_⇾̣₂_ : Family₂ → Family₂ → Set
_⇾̣₂_ = 𝔽am₂._⇒_
infixr 10 _⇾̣₂_

open import Categories.Category

module FunctorLift
  {𝕀o 𝕀ℓ 𝕀e ℂo ℂℓ ℂe 𝔻o 𝔻ℓ 𝔻e : Level}
  {𝕀 : Category 𝕀o 𝕀ℓ 𝕀e}
  {ℂ : Category ℂo ℂℓ ℂe}
  {𝔻 : Category 𝔻o 𝔻ℓ 𝔻e}
  (F : Functor ℂ 𝔻) where

  private
    module 𝕀 = Category 𝕀
    module ℂ = Category ℂ
    module 𝔻 = Category 𝔻

    open 𝔻.HomReasoning

    module F = Functor F

    lift₀ : Functor 𝕀 ℂ → Functor 𝕀 𝔻
    lift₀ G = record
      { F₀ = λ x → F.₀ (G.₀ x)
      ; F₁ = λ f → F.₁ (G.₁ f)
      ; identity = begin
        F.₁ (G.₁ 𝕀.id)
          ≈⟨ F.F-resp-≈ G.identity ⟩
        F.₁ ℂ.id
          ≈⟨ F.identity ⟩
        𝔻.id ∎
      ; homomorphism = λ{ {f = f}{g = g} → begin
        F.₁ (G.₁ (𝕀 [ g ∘ f ]))
          ≈⟨ F.F-resp-≈ G.homomorphism ⟩
        F.₁ (ℂ [ G.₁ g ∘ G.₁ f ])
          ≈⟨ F.homomorphism ⟩
        𝔻 [ F.₁ (G.₁ g) ∘ F.₁ (G.₁ f) ] ∎
        }
      ; F-resp-≈ = λ p → F.F-resp-≈ (G.F-resp-≈ p)
      } where module G = Functor G

  lift : Functor (Functors 𝕀 ℂ) (Functors 𝕀 𝔻)
  lift = record
    { F₀ = lift₀
    ; F₁ = λ {A}{B} f → ntHelper record
      { η = λ X → F.₁ (η f X)
      ; commute = λ {X}{Y} g → begin
        𝔻 [ F.₁ (η f Y) ∘ F.₁ (Functor.₁ A g) ]
          ≈⟨ ⟺ F.homomorphism ⟩
        F.₁ (ℂ [ η f Y ∘ Functor.₁ A g ])
          ≈⟨ F.F-resp-≈ (commute f g) ⟩
        F.₁ (ℂ [ Functor.F₁ B g ∘ η f X ])
          ≈⟨ F.homomorphism ⟩
        𝔻 [ F.₁ (Functor.₁ B g) ∘ F.₁ (η f X) ] ∎
      }
    ; identity = F.identity
    ; homomorphism = F.homomorphism
    ; F-resp-≈ = λ p → F.F-resp-≈ p
    } where open NT


open import Categories.Category.Product
open import Categories.Category.Product.Properties
open import Categories.Functor.Bifunctor
import Categories.Functor.Equivalence as FEquiv
open import Categories.NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism as NI using (NaturalIsomorphism ; niHelper)
import Categories.Morphism.Reasoning as MR

module BifunctorLift
  {𝕀o 𝕀ℓ 𝕀e ℂo ℂℓ ℂe 𝔻o 𝔻ℓ 𝔻e 𝔼o 𝔼ℓ 𝔼e : Level}
  {𝕀 : Category 𝕀o 𝕀ℓ 𝕀e}
  {ℂ : Category ℂo ℂℓ ℂe}
  {𝔻 : Category 𝔻o 𝔻ℓ 𝔻e}
  {𝔼 : Category 𝔼o 𝔼ℓ 𝔼e}
  (𝕀≅𝕀op : Equiv.StrongEquivalence 𝕀 (Category.op 𝕀))
  (F : Bifunctor (Category.op ℂ) 𝔻 𝔼) where

  bar : Functor (Functors 𝕀 (Product (Category.op ℂ) 𝔻)) (Functors 𝕀 𝔼)
  bar = FunctorLift.lift F

  private
    module 𝕀 = Category 𝕀
    module ℂ = Category ℂ
    module 𝔻 = Category 𝔻

    module ℂHR = ℂ.HomReasoning
    module 𝔻HR = 𝔻.HomReasoning

    baz : (X : Functor 𝕀 (Product ℂ.op 𝔻)) → NaturalIsomorphism ((πˡ ∘F X) ※ (πʳ ∘F X)) X
    baz X = NI.trans (NI.trans (※-distrib ℂ.op 𝔻 πˡ πʳ X) ((πˡ※πʳ≃id ℂ.op 𝔻) NI.ⓘʳ X)) (FEquiv._≡F_.natIso FEquiv.≡F-identityˡ)

    [𝕀,ℂop×𝔻]≅[𝕀,ℂop]×[𝕀,𝔻] : Equiv.StrongEquivalence (Functors 𝕀 (Product (Category.op ℂ) 𝔻)) (Product (Functors 𝕀 (Category.op ℂ)) (Functors 𝕀 𝔻))
    [𝕀,ℂop×𝔻]≅[𝕀,ℂop]×[𝕀,𝔻] = record
      { F = record
        { F₀ = λ x → (πˡ ∘F x) , (πʳ ∘F x)
        ; F₁ = λ f → πˡ ∘ˡ f , πʳ ∘ˡ f
        ; identity = IsEquivalence.refl ℂ.equiv , IsEquivalence.refl 𝔻.equiv
        ; homomorphism = IsEquivalence.refl ℂ.equiv , IsEquivalence.refl 𝔻.equiv
        ; F-resp-≈ = λ x → proj₁ x , proj₂ x
        }
      ; G = record
        { F₀ = λ{ (A , B) → A ※ B }
        ; F₁ = λ{ (f , g) → f ※ⁿ g }
        ; identity = IsEquivalence.refl ℂ.equiv , IsEquivalence.refl 𝔻.equiv
        ; homomorphism = IsEquivalence.refl ℂ.equiv , IsEquivalence.refl 𝔻.equiv
        ; F-resp-≈ = λ x → proj₁ x , proj₂ x
        }
      ; weak-inverse = record
        { F∘G≈id = record
          { F⇒G = ntHelper record { η = λ{ (A , B) → NaturalIsomorphism.F⇒G (project₁ {i = A}{j = B}) , NaturalIsomorphism.F⇒G (project₂ {i = A}{j = B}) } ; commute = λ _ → MR.Basic.id-comm ℂ , MR.Basic.id-comm-sym 𝔻 }
          ; F⇐G = ntHelper record { η = λ{ (A , B) → NaturalIsomorphism.F⇐G (project₁ {i = A}{j = B}) , NaturalIsomorphism.F⇐G (project₂ {i = A}{j = B}) } ; commute = λ _ → MR.Basic.id-comm ℂ , MR.Basic.id-comm-sym 𝔻 }
          ; iso = λ X → record { isoˡ = ℂ.identity² , 𝔻.identity² ; isoʳ = ℂ.identity² , 𝔻.identity² }
          }
        ; G∘F≈id = niHelper record
          { η = λ X → NaturalIsomorphism.F⇒G (baz X)
          ; η⁻¹ = λ X → NaturalIsomorphism.F⇐G (baz X)
          ; commute = λ {X}{Y} f {x} →
            (ℂHR.begin
              proj₁ (NT.η f x) ℂ.∘ (ℂ.id ℂ.∘ ℂ.id) ℂ.∘ ℂ.id
                ℂHR.≈⟨ ℂ.sym-assoc ℂHR.○ ℂ.identityʳ ℂHR.○ ℂ.sym-assoc ℂHR.○ ℂ.identityʳ ℂHR.○ ℂ.identityʳ ⟩
              proj₁ (NT.η f x)
                ℂHR.≈⟨ ℂHR.⟺ (ℂ.assoc ℂHR.○ ℂ.assoc ℂHR.○ ℂ.identityˡ ℂHR.○ ℂ.identityˡ ℂHR.○ ℂ.identityˡ) ⟩
              ((ℂ.id ℂ.∘ ℂ.id) ℂ.∘ ℂ.id) ℂ.∘ proj₁ (NT.η f x)
            ℂHR.∎) , (𝔻HR.begin
              (𝔻.id 𝔻.∘ 𝔻.id 𝔻.∘ 𝔻.id) 𝔻.∘ proj₂ (NT.η f x)
                𝔻HR.≈⟨ 𝔻.assoc 𝔻HR.○ 𝔻.identityˡ 𝔻HR.○ 𝔻.assoc 𝔻HR.○ 𝔻.identityˡ 𝔻HR.○ 𝔻.identityˡ ⟩
              proj₂ (NT.η f x)
                𝔻HR.≈⟨ 𝔻HR.⟺ (𝔻.sym-assoc 𝔻HR.○ 𝔻.sym-assoc 𝔻HR.○ 𝔻.identityʳ 𝔻HR.○ 𝔻.identityʳ 𝔻HR.○ 𝔻.identityʳ) ⟩
              proj₂ (NT.η f x) 𝔻.∘ 𝔻.id 𝔻.∘ 𝔻.id 𝔻.∘ 𝔻.id
            𝔻HR.∎)
          ; iso = λ X → record
            { isoˡ = (ℂ.sym-assoc ℂHR.○ ℂ.sym-assoc ℂHR.○ ℂ.identityʳ ℂHR.○ ℂ.identityʳ ℂHR.○ ℂ.identityʳ ℂHR.○ ℂ.identityʳ ℂHR.○ ℂ.identityʳ)
                   , (𝔻.sym-assoc 𝔻HR.○ 𝔻.sym-assoc 𝔻HR.○ 𝔻.identityʳ 𝔻HR.○ 𝔻.identityʳ 𝔻HR.○ 𝔻.identityʳ 𝔻HR.○ 𝔻.identityʳ 𝔻HR.○ 𝔻.identityʳ)
            ; isoʳ = (ℂ.sym-assoc ℂHR.○ ℂ.identityʳ ℂHR.○ ℂ.sym-assoc ℂHR.○ ℂ.identityʳ ℂHR.○ ℂ.identityʳ ℂHR.○ ℂ.sym-assoc ℂHR.○ ℂ.identityʳ ℂHR.○ ℂ.identityʳ)
                   , (𝔻.sym-assoc 𝔻HR.○ 𝔻.identityʳ 𝔻HR.○ 𝔻.sym-assoc 𝔻HR.○ 𝔻.identityʳ 𝔻HR.○ 𝔻.identityʳ 𝔻HR.○ 𝔻.sym-assoc 𝔻HR.○ 𝔻.identityʳ 𝔻HR.○ 𝔻.identityʳ) }
          }
        }
      }

    module 𝕀≅𝕀op = Equiv.StrongEquivalence 𝕀≅𝕀op
    module [𝕀,ℂop×𝔻]≅[𝕀,ℂop]×[𝕀,𝔻] = Equiv.StrongEquivalence [𝕀,ℂop×𝔻]≅[𝕀,ℂop]×[𝕀,𝔻]

--     lift₀ : Functor 𝕀 ℂ.op × Functor 𝕀 𝔻 → Functor 𝕀 𝔼
--     lift₀ (A , B) = record
--       { F₀ = λ x → F.₀ (A.₀ x , B.₀ x)
--       ; F₁ = λ {X}{Y} f → F.₁ (A.₁ f , B.₁ f)
--       ; identity = {!   !}
--       ; homomorphism = {!   !}
--       ; F-resp-≈ = {!   !}
--       } where module A = Functor A ; module B = Functor B
--
  lift : Bifunctor (Category.op (Functors 𝕀 ℂ)) (Functors 𝕀 𝔻) (Functors 𝕀 𝔼)
  lift = (FunctorLift.lift F) ∘F [𝕀,ℂop×𝔻]≅[𝕀,ℂop]×[𝕀,𝔻].G ∘F (opF⇒ ∘F record
    { F₀ = λ x → x ∘F 𝕀≅𝕀op.G
    ; F₁ = λ f → f ∘ʳ 𝕀≅𝕀op.G
    ; identity = IsEquivalence.refl ℂ.equiv
    ; homomorphism = IsEquivalence.refl ℂ.equiv
    ; F-resp-≈ = λ x → x
    } ⁂ idF)

_² : Functor 𝔽amiliesₛ 𝔽amiliesₛ → Functor 𝔽amilies₂ 𝔽amilies₂
_² = FunctorLift.lift

_²₂ : Bifunctor 𝔽amₛ.op 𝔽amiliesₛ 𝔽amiliesₛ → Bifunctor 𝔽am₂.op 𝔽amilies₂ 𝔽amilies₂
_²₂ = {! BifunctorLift.lift  !}

_ᴷ : Familyₛ → Family₂
_ᴷ 𝒜 = record
  { F₀ = λ 𝔐 → 𝒜
  ; F₁ = λ f z → z
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ _ → refl
  }
