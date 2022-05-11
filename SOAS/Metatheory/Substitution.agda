
open import SOAS.Common
open import SOAS.Families.Core
open import Categories.Object.Initial
open import SOAS.Coalgebraic.Strength
import SOAS.Metatheory.MetaAlgebra
import SOAS.Context

-- Substitution structure by initiality
module SOAS.Metatheory.Substitution {T : Set}
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

open import SOAS.Abstract.Monoid

open import SOAS.Coalgebraic.Map
open import SOAS.Coalgebraic.Monoid
open import SOAS.Coalgebraic.Lift

open import SOAS.Metatheory.Algebra ⅀F
open import SOAS.Metatheory.Contextual [_]_
open import SOAS.Metatheory.Semantics [_]_ ⅀F ⅀:Str 𝕋:Init
open import SOAS.Metatheory.Traversal [_]_ ⅀F ⅀:Str 𝕋:Init
open import SOAS.Metatheory.Renaming [_]_ ⅀F ⅀:Str 𝕋:Init
open import SOAS.Metatheory.Coalgebraic [_]_ ⅀F ⅀:Str 𝕋:Init

open Strength ⅀:Str

private
  variable
    Γ Δ : Ctx
    α β : T

-- Substitution is a 𝕋-parametrised traversal into 𝕋
module Substitution = Traversal 𝕋ᴮ 𝕒𝕝𝕘 id 𝕞𝕧𝕒𝕣 𝕓𝕠𝕩

𝕤𝕦𝕓 : 𝕋 ⇾̣₂ 〖 𝕋 , 𝕋 〗²
𝕤𝕦𝕓 = Substitution.𝕥𝕣𝕒𝕧

-- The renaming and algebra structures on 𝕋 are compatible, so 𝕤𝕦𝕓 is coalgebraic
𝕤𝕦𝕓ᶜ : {𝔐 : MCtx} → Coalgebraic 𝕋ᴮ 𝕋ᴮ 𝕋ᴮ (𝕤𝕦𝕓 {𝔐})
𝕤𝕦𝕓ᶜ = Travᶜ.𝕥𝕣𝕒𝕧ᶜ 𝕋ᴮ 𝕒𝕝𝕘 id 𝕞𝕧𝕒𝕣 𝕓𝕠𝕩 𝕋ᴮ idᴮ⇒ Renaming.𝕤𝕖𝕞ᵃ⇒

module 𝕤𝕦𝕓ᶜ {𝔐} = Coalgebraic (𝕤𝕦𝕓ᶜ {𝔐})

-- Compatibility of renaming and substitution
compat : {𝔐 : MCtx}{ρ : Γ ↝ Δ} (t : 𝕋 𝔐 α Γ) → 𝕣𝕖𝕟 t ρ ≡ 𝕤𝕦𝕓 t (𝕧𝕒𝕣 ∘ ρ)
compat {ρ = ρ} t =  begin 𝕣𝕖𝕟 t ρ           ≡˘⟨ 𝕥𝕣𝕒𝕧-η≈id 𝕋ᴮ id refl ⟩
                          𝕤𝕦𝕓 (𝕣𝕖𝕟 t ρ) 𝕧𝕒𝕣  ≡⟨ 𝕤𝕦𝕓ᶜ.f∘r ⟩
                          𝕤𝕦𝕓 t (𝕧𝕒𝕣 ∘ ρ)   ∎ where open ≡-Reasoning

-- Substitution associativity law
𝕤𝕦𝕓-comp : MapEq₂ 𝕋ᴮ 𝕋ᴮ 𝕒𝕝𝕘 𝕓𝕠𝕩 (λ t σ ς → 𝕤𝕦𝕓 (𝕤𝕦𝕓 t σ) ς)
                           (λ t σ ς → 𝕤𝕦𝕓 t (λ v → 𝕤𝕦𝕓 (σ v) ς))
𝕤𝕦𝕓-comp = record
  { φ = id
  ; ϕ = 𝕤𝕦𝕓
  ; χ = 𝕞𝕧𝕒𝕣
  ; f⟨𝑣⟩ = 𝕥≈₁ 𝕥⟨𝕧⟩
  ; f⟨𝑚⟩ = trans (𝕥≈₁ 𝕥⟨𝕞⟩) 𝕥⟨𝕞⟩
  ; f⟨𝑎⟩ = λ{ {𝔐 = 𝔐}{σ = σ}{ς}{t} → begin
        𝕤𝕦𝕓 (𝕤𝕦𝕓 (𝕒𝕝𝕘 t) σ) ς
    ≡⟨ 𝕥≈₁ 𝕥⟨𝕒⟩ ⟩
        𝕤𝕦𝕓 (𝕒𝕝𝕘 (str 𝕋ᴮ (𝕋 𝔐) (⅀₁ 𝕤𝕦𝕓 t) σ)) ς
    ≡⟨ 𝕥⟨𝕒⟩ ⟩
        𝕒𝕝𝕘 (str 𝕋ᴮ (𝕋 𝔐) (⅀₁ 𝕤𝕦𝕓 (str 𝕋ᴮ (𝕋 𝔐) (⅀₁ 𝕤𝕦𝕓 t) σ)) ς)
    ≡˘⟨ congr (str-nat₂ 𝕤𝕦𝕓 (⅀₁ 𝕤𝕦𝕓 t) σ) (λ - → 𝕒𝕝𝕘 (str 𝕋ᴮ (𝕋 𝔐) - ς)) ⟩
        𝕒𝕝𝕘 (str 𝕋ᴮ (𝕋 𝔐) (str 𝕋ᴮ (〖 𝕋 , 𝕋 〗² 𝔐) (⅀.F₁ (λ { h ς → 𝕤𝕦𝕓 (h ς) }) (⅀₁ 𝕤𝕦𝕓 t)) σ) ς)
    ≡˘⟨ congr ⅀.homomorphism (λ - → 𝕒𝕝𝕘 (str 𝕋ᴮ (𝕋 𝔐) (str 𝕋ᴮ (〖 𝕋 , 𝕋 〗² 𝔐) - σ) ς)) ⟩
        𝕒𝕝𝕘 (str 𝕋ᴮ (𝕋 𝔐) (str 𝕋ᴮ (〖 𝕋 , 𝕋 〗² 𝔐) (⅀₁ (λ{ t σ → 𝕤𝕦𝕓 (𝕤𝕦𝕓 t σ)}) t) σ) ς)
    ∎ }
  ; f⟨𝑏⟩ = trans (𝕥≈₁ 𝕥⟨𝕓⟩) 𝕥⟨𝕓⟩
  ; g⟨𝑣⟩ = 𝕥⟨𝕧⟩
  ; g⟨𝑚⟩ = 𝕥⟨𝕞⟩
  ; g⟨𝑎⟩ = λ{ {𝔐 = 𝔐}{σ = σ}{ς}{t} → begin
        𝕤𝕦𝕓 (𝕒𝕝𝕘 t) (λ v → 𝕤𝕦𝕓 (σ v) ς)
    ≡⟨ 𝕥⟨𝕒⟩ ⟩
        𝕒𝕝𝕘 (str 𝕋ᴮ (𝕋 𝔐) (⅀₁ 𝕤𝕦𝕓 t) (λ v → 𝕤𝕦𝕓 (σ v) ς))
    ≡⟨ cong 𝕒𝕝𝕘 (str-dist (𝕋 𝔐) 𝕤𝕦𝕓ᶜ (⅀₁ 𝕤𝕦𝕓 t) (λ {τ} z → σ z) ς) ⟩
        𝕒𝕝𝕘 (str 𝕋ᴮ (𝕋 𝔐) (str 𝕋ᴮ (〖 𝕋 , 𝕋 〗² 𝔐) (⅀.F₁ (precomp (𝕋 𝔐) 𝕤𝕦𝕓) (⅀₁ 𝕤𝕦𝕓 t)) σ) ς)
    ≡˘⟨ congr ⅀.homomorphism (λ - → 𝕒𝕝𝕘 (str 𝕋ᴮ (𝕋 𝔐) (str 𝕋ᴮ (〖 𝕋 , 𝕋 〗² 𝔐) - σ) ς)) ⟩
        𝕒𝕝𝕘 (str 𝕋ᴮ (𝕋 𝔐) (str 𝕋ᴮ (〖 𝕋 , 𝕋 〗² 𝔐) (⅀₁ (λ{ t σ ς → 𝕤𝕦𝕓 t (λ v → 𝕤𝕦𝕓 (σ v) ς)}) t) σ) ς)
    ∎ }
  ; g⟨𝑏⟩ = λ{ {Γ = Γ}{α = α}{𝔐 = 𝔐}{σ = σ}{ς}{b} → trans 𝕥⟨𝕓⟩ (cong 𝕓𝕠𝕩 (BF:Str.str-dist (𝕋 𝔐) 𝕤𝕦𝕓ᶜ (B₁ 𝕤𝕦𝕓 {α}{Γ} b) (λ {τ} z → σ z) ς)) }
  } where open ≡-Reasoning ; open Substitution

-- Coalgebraic monoid structure on 𝕋
𝕋ᵐ : {𝔐 : MCtx} → Mon (𝕋 𝔐)
𝕋ᵐ = record
  { η = 𝕧𝕒𝕣
  ; μ = 𝕤𝕦𝕓
  ; lunit = Substitution.𝕥⟨𝕧⟩
  ; runit = λ{ {t = t} → trans (𝕥𝕣𝕒𝕧-η≈𝕤𝕖𝕞 𝕋ᴮ 𝕋ᵃ id refl) 𝕤𝕖𝕞-id }
  ; assoc = λ{ {t = t} → MapEq₂.≈ 𝕤𝕦𝕓-comp t }
  }

open module - {𝔐} = Mon (𝕋ᵐ {𝔐}) using ([_/] ; [_,_/]₂ ; lunit ; runit ; assoc) public

𝕋ᴹ : {𝔐 : MCtx} → CoalgMon (𝕋 𝔐)
𝕋ᴹ = record { ᴮ = 𝕋ᴮ ; ᵐ = 𝕋ᵐ ; η-compat = refl ; μ-compat = λ{ {t = t} → compat t } }


-- Corollaries: renaming and simultaneous substitution commutes with
-- single-variable substitution
open import SOAS.ContextMaps.Combinators
𝕣𝕖𝕟[/] : {𝔐 : MCtx}(ρ : Γ ↝ Δ)(b : 𝕋 𝔐 α (β ∙ Γ))(a : 𝕋 𝔐 β Γ)
      → 𝕣𝕖𝕟 ([ a /] b) ρ ≡ [ (𝕣𝕖𝕟 a ρ) /] (𝕣𝕖𝕟 b (rlift _ ρ))
𝕣𝕖𝕟[/] {𝔐 = 𝔐} ρ b a = begin
      𝕣𝕖𝕟 ([ a /] b) ρ
  ≡⟨ 𝕤𝕦𝕓ᶜ.r∘f ⟩
      𝕤𝕦𝕓 b (λ v → 𝕣𝕖𝕟 (add (𝕋 𝔐) a 𝕧𝕒𝕣 v) ρ)
  ≡⟨ cong (𝕤𝕦𝕓 b) (dext (λ{ new → refl ; (old y) → Renaming.𝕥⟨𝕧⟩})) ⟩
      𝕤𝕦𝕓 b (λ v → add (𝕋 𝔐) (𝕣𝕖𝕟  a ρ) 𝕧𝕒𝕣 (rlift _ ρ v))
  ≡˘⟨ 𝕤𝕦𝕓ᶜ.f∘r ⟩
      [ 𝕣𝕖𝕟 a ρ /] (𝕣𝕖𝕟 b (rlift _ ρ))
  ∎ where open ≡-Reasoning

𝕤𝕦𝕓[/] : {𝔐 : MCtx}(σ : Γ ~[ 𝕋 𝔐 ]↝ Δ)(b : 𝕋 𝔐 α (β ∙ Γ))(a : 𝕋 𝔐 β Γ)
      → 𝕤𝕦𝕓 ([ a /] b) σ ≡ [ 𝕤𝕦𝕓 a σ /] (𝕤𝕦𝕓 b (lift 𝕋ᴮ ⌈ β ⌋ σ))
𝕤𝕦𝕓[/] {β = β}{𝔐 = 𝔐} σ b a = begin
      𝕤𝕦𝕓 ([ a /] b) σ
  ≡⟨ assoc ⟩
      𝕤𝕦𝕓 b (λ v → 𝕤𝕦𝕓 (add (𝕋 𝔐) a 𝕧𝕒𝕣 v) σ)
  ≡⟨ cong (𝕤𝕦𝕓 b) (dext (λ{ new → sym lunit ; (old v) → sym (begin
        𝕤𝕦𝕓 (𝕣𝕖𝕟 (σ v) old) (add (𝕋 𝔐) (𝕤𝕦𝕓 a σ) 𝕧𝕒𝕣)
    ≡⟨ 𝕤𝕦𝕓ᶜ.f∘r ⟩
        𝕤𝕦𝕓 (σ v) (λ v → add (𝕋 𝔐) (𝕤𝕦𝕓 a σ) 𝕧𝕒𝕣 (old v))
    ≡⟨ cong (𝕤𝕦𝕓 (σ v)) (dext (λ{ new → refl ; (old v) → refl})) ⟩
        𝕤𝕦𝕓 (σ v) 𝕧𝕒𝕣
    ≡⟨ runit ⟩
        σ v
    ≡˘⟨ lunit ⟩
        𝕤𝕦𝕓 (𝕧𝕒𝕣 v) σ
    ∎)})) ⟩
      𝕤𝕦𝕓 b (λ v → 𝕤𝕦𝕓 (lift 𝕋ᴮ ⌈ β ⌋ σ v) (add (𝕋 𝔐) (𝕤𝕦𝕓 a σ) 𝕧𝕒𝕣))
  ≡˘⟨ assoc ⟩
      [ 𝕤𝕦𝕓 a σ /] (𝕤𝕦𝕓 b (lift 𝕋ᴮ ⌈ β ⌋ σ))
  ∎ where open ≡-Reasoning
