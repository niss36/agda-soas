module STCMTT.Syntax where

open import SOAS.Common
open import SOAS.Context
open import SOAS.Variable
open import SOAS.Families.Core
open import SOAS.Construction.Structure
open import SOAS.ContextMaps.Inductive

open import SOAS.Metatheory.Syntax

open import STCMTT.Signature

private
  variable
    Γ Δ Π : Ctx
    α β : ΛT
    𝔐 : MCtx

-- Inductive term declaration
module Λ:Terms where

  data Λ : Family₂ where
    var  : (ℐ ᴷ) ⇾̣₂ Λ
    mvar : Π ⊩ α ∈ 𝔐 → Sub (Λ 𝔐) Π Γ → Λ 𝔐 α Γ
    box : (Ψ : Ctx {ΛT}) → Λ 𝔐 α Ψ → Λ 𝔐 ([ Ψ ] α) Γ

    _$_ : Λ 𝔐 (α ↣ β) Γ → Λ 𝔐 α Γ → Λ 𝔐 β Γ
    ƛ_  : Λ 𝔐 β (α ∙ Γ) → Λ 𝔐 (α ↣ β) Γ

  infixl 20 _$_
  infixr 10 ƛ_

  open import SOAS.Metatheory.MetaAlgebra ⅀F [_]_

  Λᵃ : MetaAlg Λ
  Λᵃ = record
    { 𝑎𝑙𝑔 = λ where
      (appₒ ⋮ a , b) → _$_ a b
      (lamₒ ⋮ a)     → ƛ_  a
    ; 𝑣𝑎𝑟 = var ; 𝑚𝑣𝑎𝑟 = λ 𝔪 mε → mvar 𝔪 (tabulate mε)
    ; 𝑏𝑜𝑥 = λ {Ψ : Ctx} → box Ψ }

  module Λᵃ = MetaAlg Λᵃ

  module _ {𝓐 : Family₂}(𝓐ᵃ : MetaAlg 𝓐) where

    open MetaAlg 𝓐ᵃ

    𝕤𝕖𝕞 : Λ ⇾̣₂ 𝓐
    𝕊 : Sub (Λ 𝔐) Π Γ → Π ~[ 𝓐 𝔐 ]↝ Γ
    𝕊 (t ◂ σ) new = 𝕤𝕖𝕞 t
    𝕊 (t ◂ σ) (old v) = 𝕊 σ v
    𝕤𝕖𝕞 (mvar 𝔪 mε) = 𝑚𝑣𝑎𝑟 𝔪 (𝕊 mε)
    𝕤𝕖𝕞 (var v) = 𝑣𝑎𝑟 v
    𝕤𝕖𝕞 (box Ψ b) = 𝑏𝑜𝑥 (𝕤𝕖𝕞 b)

    𝕤𝕖𝕞 (_$_ a b) = 𝑎𝑙𝑔 (appₒ ⋮ 𝕤𝕖𝕞 a , 𝕤𝕖𝕞 b)
    𝕤𝕖𝕞 (ƛ_  a)   = 𝑎𝑙𝑔 (lamₒ ⋮ 𝕤𝕖𝕞 a)

    𝕤𝕖𝕞ᵃ⇒ : MetaAlg⇒ Λᵃ 𝓐ᵃ 𝕤𝕖𝕞
    𝕤𝕖𝕞ᵃ⇒ = record
      { ⟨𝑎𝑙𝑔⟩ = λ{ {t = t} → ⟨𝑎𝑙𝑔⟩ t }
      ; ⟨𝑣𝑎𝑟⟩ = refl
      ; ⟨𝑚𝑣𝑎𝑟⟩ = λ{ {𝔪 = 𝔪}{mε} → cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-tab mε)) }
      ; ⟨𝑏𝑜𝑥⟩ = refl }
      where
      open ≡-Reasoning
      ⟨𝑎𝑙𝑔⟩ : (t : ⅀ (Λ 𝔐) α Γ) → 𝕤𝕖𝕞 (Λᵃ.𝑎𝑙𝑔 t) ≡ 𝑎𝑙𝑔 (⅀₁ 𝕤𝕖𝕞 t)
      ⟨𝑎𝑙𝑔⟩ (appₒ ⋮ _) = refl
      ⟨𝑎𝑙𝑔⟩ (lamₒ ⋮ _) = refl

      𝕊-tab : (mε : Π ~[ Λ 𝔐 ]↝ Γ)(v : ℐ α Π) → 𝕊 (tabulate mε) v ≡ 𝕤𝕖𝕞 (mε v)
      𝕊-tab mε new = refl
      𝕊-tab mε (old v) = 𝕊-tab (mε ∘ old) v

    module _ (g : Λ ⇾̣₂ 𝓐)(gᵃ⇒ : MetaAlg⇒ Λᵃ 𝓐ᵃ g) where

      open MetaAlg⇒ gᵃ⇒

      𝕤𝕖𝕞! : (t : Λ 𝔐 α Γ) → 𝕤𝕖𝕞 t ≡ g t
      𝕊-ix : (mε : Sub (Λ 𝔐) Π Γ)(v : ℐ α Π) → 𝕊 mε v ≡ g (index mε v)
      𝕊-ix (x ◂ mε) new = 𝕤𝕖𝕞! x
      𝕊-ix (x ◂ mε) (old v) = 𝕊-ix mε v
      𝕤𝕖𝕞! (mvar 𝔪 mε) rewrite cong (𝑚𝑣𝑎𝑟 𝔪) (dext (𝕊-ix mε))
        = trans (sym ⟨𝑚𝑣𝑎𝑟⟩) (cong (g ∘ mvar 𝔪) (tab∘ix≈id mε))
      𝕤𝕖𝕞! (var v) = sym ⟨𝑣𝑎𝑟⟩
      𝕤𝕖𝕞! (box Ψ b) rewrite 𝕤𝕖𝕞! b = sym ⟨𝑏𝑜𝑥⟩

      𝕤𝕖𝕞! (_$_ a b) rewrite 𝕤𝕖𝕞! a | 𝕤𝕖𝕞! b = sym ⟨𝑎𝑙𝑔⟩
      𝕤𝕖𝕞! (ƛ_ a) rewrite 𝕤𝕖𝕞! a = sym ⟨𝑎𝑙𝑔⟩


-- Syntax instance for the signature
Λ:Syn : Syntax [_]_
Λ:Syn = record
  { ⅀F = ⅀F
  ; ⅀:CS = ⅀:CompatStr
  ; mvarᵢ = Λ:Terms.mvar
  ; 𝕋:Init = let open Λ:Terms in record
    { ⊥ = Λ ⋉ Λᵃ
    ; ⊥-is-initial = record { ! = λ{ {𝓐 ⋉ 𝓐ᵃ} → 𝕤𝕖𝕞 𝓐ᵃ ⋉ 𝕤𝕖𝕞ᵃ⇒ 𝓐ᵃ }
    ; !-unique = λ{ {𝓐 ⋉ 𝓐ᵃ} (f ⋉ fᵃ⇒) {x = t} → 𝕤𝕖𝕞! 𝓐ᵃ f fᵃ⇒ t } } } }

-- Instantiation of the syntax and metatheory
open Syntax Λ:Syn public
open Λ:Terms public
open import SOAS.Families.Build public
open import SOAS.Syntax.Shorthands [_]_ Λᵃ public
open import SOAS.Metatheory [_]_ Λ:Syn public
