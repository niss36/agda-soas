open import SOAS.Common

open import Data.Bool
open import Data.Nat
open import Data.Nat.Show renaming (show to showNat)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _++_)

open import Categories.Object.Initial

import SOAS.Context
import SOAS.Syntax.Signature
import SOAS.Metatheory.MetaAlgebra

module SOAS.PrettyPrint {T : Set}
  (open SOAS.Context {T})
  (showT : T → String)
  (showCtx : {A : Set} → (A → A) → (A → String → String) → A → Ctx → String)
  ([_]_ : Ctx → T → T)
  (open SOAS.Syntax.Signature T)
  {O : Set}(𝕋:Sig : Signature O)
  (showOp : O → String)
  (open Signature 𝕋:Sig)
  (open SOAS.Metatheory.MetaAlgebra {T} [_]_ ⅀F)
  (𝕋:Init : Initial (𝕄etaAlgebras)) where

open import SOAS.Variable
open import SOAS.Families.Core {T}

withDot : Bool → String → String
withDot false s = s
withDot true s = s ++ ". "

-- Operations on contexts

len : Ctx → ℕ
len ∅ = ℕ.zero
len (α ∙ Γ) = suc (len Γ)

showVar : ℕ → String → String
showVar n t = "x" ++ (showNat n) ++ ": " ++ t

showCtxBinder : ℕ → Ctx → Bool → Bool → String
showCtxBinder n ∅ false _ = ""
showCtxBinder n ∅ true b = withDot b "∅"
showCtxBinder n (α ∙ Γ) _ b = withDot b (showCtx pred showVar (n + len Γ) (α ∙ Γ))

-- Operations on metavariable contexts

mlen : MCtx → ℕ
mlen ⁅⁆ = ℕ.zero
mlen (⁅ Π ⊩ₙ τ ⁆ 𝔐) = suc (mlen 𝔐)

showMvar : ℕ → String → String
showMvar m s = "𝔪" ++ (showNat m) ++ ": " ++ s

showMT : Ctx → T → String
showMT Π τ = "[" ++ (showCtx id (λ _ → id) "" Π) ++ " ⊩ " ++ showT τ ++ "]"

showMCtx : {A : Set} → (A → A) → (A → String → String) → A → MCtx → String
showMCtx next f a ⁅⁆ = "⁅⁆"
showMCtx next f a ⁅ Π ⊩ₙ τ ⁆̣ = f a (showMT Π τ)
showMCtx next f a (⁅ Π ⊩ₙ τ ⁆ (⁅ Π₁ ⊩ₙ τ₁ ⁆ 𝔐)) = (showMCtx next f (next a) (⁅ Π₁ ⊩ₙ τ₁ ⁆ 𝔐)) ++ ", " ++ f a (showMT Π τ)

showMCtxBinder : ℕ → MCtx → Bool → Bool → String
showMCtxBinder m ⁅⁆ false _ = ""
showMCtxBinder m ⁅⁆ true b = withDot b "⁅⁆"
showMCtxBinder m (⁅ Π ⊩ₙ τ ⁆ 𝔐) _ b = withDot b (showMCtx pred showMvar (m + mlen 𝔐) (⁅ Π ⊩ₙ τ ⁆ 𝔐))

-- Pretty printing environment:
-- ( m distinct metavariables* , maps from metavariables to integers ,
--   n distinct     variables* , maps from     variables to integers )
-- *in the entire expression (not just this fragment)
Env : MCtx → Ctx → Set
Env 𝔐 Γ = ℕ × ({Ψ : Ctx}{α : T} → Ψ ⊩ α ∈ 𝔐 → ℕ) × ℕ × ({τ : T} → ℐ τ Γ → ℕ)

-- Monad structure

ret : {A : Set} → String → A → String × A
ret s a = (s , a)

-- f then g; threads along the environment and concatenates the strings.
_●_ : {A B C : Set} → (A → String × B) → (B → String × C) → (A → String × C)
(f ● g) a = let (s , b) = f a
                (t , c) = g b
            in (s ++ t , c)

infixr 10 _●_

-- same but with a ", " added inbetween
_●,_ : {A B C : Set} → (A → String × B) → (B → String × C) → (A → String × C)
(f ●, g) = f ● (ret ", ") ● g

infixr 20 _●,_

-- Binding variables

bindAux : {𝔐 : MCtx}{Γ : Ctx}(Θ : Ctx) → Env 𝔐 Γ → Env 𝔐 (Θ ∔ Γ)
bindAux ∅ e = e
bindAux (α ∙ Θ) e = let (m , ρ , n , ϱ) = bindAux Θ e in (m , ρ , suc n , λ{ new → n ; (old v) → ϱ v })

unbindAux : {𝔐 : MCtx}{Γ : Ctx}(Θ : Ctx) → Env 𝔐 (Θ ∔ Γ) → Env 𝔐 Γ
unbindAux ∅ e = e
unbindAux (α ∙ Θ) (m , ρ , n , ϱ) = unbindAux Θ (m , ρ , n , λ v → ϱ (old v))

-- Binding metavariables

-- Meta-context concatenation
_m∔_ : MCtx → MCtx → MCtx
⁅⁆ m∔ 𝔑 = 𝔑
(⁅ Π ⊩ₙ τ ⁆ 𝔐) m∔ 𝔑 = ⁅ Π ⊩ₙ τ ⁆ (𝔐 m∔ 𝔑)
infixl 20 _m∔_

mBindAux : {𝔐 : MCtx}{Γ : Ctx}(𝔑 : MCtx) → Env 𝔐 Γ → Env (𝔑 m∔ 𝔐) Γ
mBindAux ⁅⁆ e = e
mBindAux (⁅ Π ⊩ₙ τ ⁆ 𝔑) e = let (m , ρ , n , ϱ) = mBindAux 𝔑 e in (suc m , (λ{ ↓ → m ; (↑ 𝔪) → ρ 𝔪 }) , n , ϱ)

mUnbindAux : {𝔐 : MCtx}{Γ : Ctx}(𝔑 : MCtx) → Env (𝔑 m∔ 𝔐) Γ → Env 𝔐 Γ
mUnbindAux ⁅⁆ e = e
mUnbindAux (⁅ Π ⊩ₙ τ ⁆ 𝔑) (m , ρ , n , ϱ) = mUnbindAux 𝔑 (m , (λ 𝔪 → ρ (↑ 𝔪)) , n , ϱ)

module _ where

  𝓟𝓟 : Family₂
  𝓟𝓟 𝔐 τ Γ = Env 𝔐 Γ → (String × Env 𝔐 Γ)

  open import SOAS.Syntax.Arguments {T}

  -- Operators
  ppAlgArgs : {𝔐 : MCtx}{Γ : Ctx} → (op : O) → (a : List (Ctx × T)) → Arg a (𝓟𝓟 𝔐) Γ → 𝓟𝓟 𝔐 (Sort op) Γ
  ppAlgArgs {𝔐}{Γ} op a args = rec a args
    where bind : (Θ : Ctx) → Env 𝔐 Γ → (String × Env 𝔐 (Θ ∔ Γ))
          bind Θ (m , ρ , n , ϱ) = (showCtxBinder n Θ false true , bindAux Θ (m , ρ , n , ϱ))

          unbind : (Θ : Ctx) → Env 𝔐 (Θ ∔ Γ) → (String × Env 𝔐 Γ)
          unbind Θ e = ("", unbindAux Θ e)

          rec : (a : List (Ctx × T)) → Arg a (𝓟𝓟 𝔐) Γ → 𝓟𝓟 𝔐 (Sort op) Γ
          rec [] args = ret ""
          rec ((Θ , τ) ∷ []) f = bind Θ ● f ● unbind Θ
          rec ((Θ , τ) ∷ x ∷ as) (f , args) = bind Θ ● f ● unbind Θ ●, (rec (x ∷ as) args)

  ppAlg : {𝔐 : MCtx}{τ : T}{Γ : Ctx} → Σ[ op ∈ O ] (τ ≡ Sort op × Arg (Arity op) (𝓟𝓟 𝔐) Γ) → 𝓟𝓟 𝔐 τ Γ
  ppAlg {𝔐}{τ}{Γ} (op ⋮ args) = ret (showOp op ++ "(") ● (ppAlgArgs {𝔐}{Γ} op (Arity op) args) ● (ret ")")

  -- Variables
  ppVar : {𝔐 : MCtx}{τ : T}{Γ : Ctx} → ℐ τ Γ → 𝓟𝓟 𝔐 τ Γ
  ppVar {𝔐}{τ}{Γ} v (m , ρ , n , ϱ) = "x" ++ showNat (ϱ v) , m , ρ , n , ϱ

  -- Metavariables
  ppMvarArgs : {𝔐 : MCtx}{τ : T}{Δ : Ctx} → (Γ : Ctx) → (Γ ~[ 𝓟𝓟 𝔐 ]↝ Δ) → 𝓟𝓟 𝔐 τ Δ
  ppMvarArgs {𝔐}{τ}{Δ} Γ ε = rec Γ ε
    where rec : (Γ : Ctx) → (Γ ~[ 𝓟𝓟 𝔐 ]↝ Δ) → 𝓟𝓟 𝔐 τ Δ
          rec ∅ ε = ret ""
          rec (α ∙ ∅) ε = ε {α} new
          rec (α ∙ β ∙ Γ) ε = (ε {α} new) ●, (rec (β ∙ Γ) (λ v → ε (old v)))

  ppMvar : {𝔐 : MCtx}{τ : T}{Γ : Ctx} → (Γ ⊩ τ ∈ 𝔐) → {Δ : Ctx} → (Γ ~[ 𝓟𝓟 𝔐 ]↝ Δ) → 𝓟𝓟 𝔐 τ Δ
  ppMvar {𝔐}{τ}{Γ} 𝔪 {Δ} ε mn =
    let (pp , m , ρ , n , ϱ) = ppMvarArgs {𝔐}{τ}{Δ} Γ ε mn
    in "𝔪" ++ showNat (ρ 𝔪) ++ "⟨" ++ pp ++ "⟩" , m , ρ , n , ϱ

  open import SOAS.Metatheory.Contextual [_]_

  -- Box
  ppBox : {𝔐 : MCtx}{τ : T}{Γ : Ctx} → B (𝓟𝓟 𝔐) τ Γ → 𝓟𝓟 𝔐 τ Γ
  ppBox {𝔐}{τ}{Γ} (Ψ , α , eq , f) e = ((ret "box(") ● replace ● f ● remember e ● (ret ")")) e
    where replaceAux : (Ψ : Ctx) → Env 𝔐 Γ → Env 𝔐 Ψ
          replaceAux ∅ (m , ρ , n , ϱ) = (m , ρ , n , λ())
          replaceAux (α ∙ Ψ) e = let (m , ρ , n , ϱ) = replaceAux Ψ e in (m , ρ , suc n , λ{ new → n ; (old v) → ϱ v })

          replace : Env 𝔐 Γ → (String × Env 𝔐 Ψ)
          replace (m , ρ , n , ϱ) = showCtxBinder n Ψ true true , replaceAux Ψ (m , ρ , n , ϱ)

          remember : Env 𝔐 Γ → Env 𝔐 Ψ → (String × Env 𝔐 Γ)
          remember (_ , _ , _ , ϱ) (m , ρ , n , _) = ("", m , ρ , n , ϱ)

  -- Letbox
  ppLetbox : {𝔐 : MCtx}{τ : T}{Γ : Ctx} → LB 𝓟𝓟 𝔐 τ Γ → 𝓟𝓟 𝔐 τ Γ
  ppLetbox {𝔐}{τ}{Γ} (Ψ , α , f , g) = (ret "letbox(") ● f ●, bind ● g ● unbind ● (ret ")")
    where bind : Env 𝔐 Γ → (String × Env (⁅ Ψ ⊩ₙ α ⁆ 𝔐) Γ)
          bind (m , ρ , n , ϱ) = showMCtxBinder m ⁅ Ψ ⊩ₙ α ⁆̣ false true , mBindAux ⁅ Ψ ⊩ₙ α ⁆̣ (m , ρ , n , ϱ)

          unbind : Env (⁅ Ψ ⊩ₙ α ⁆ 𝔐) Γ → (String × Env 𝔐 Γ)
          unbind e = "", mUnbindAux ⁅ Ψ ⊩ₙ α ⁆̣ e

  𝓟𝓟ᵃ : MetaAlg 𝓟𝓟
  𝓟𝓟ᵃ = record {
        𝑎𝑙𝑔 = ppAlg
      ; 𝑣𝑎𝑟 = ppVar
      ; 𝑚𝑣𝑎𝑟 = ppMvar
      ; 𝑏𝑜𝑥 = ppBox
      -- ; 𝑙𝑒𝑡𝑏𝑜𝑥 = ppLetbox
      --λ { (Ψ , α , (fst , fm , fn) , (snd , sm , sn)) → "letbox(" ++ fst ++ ", " ++ "𝔪" ++ (showNat sm) ++ ": " ++ (showCtx sn Ψ) ++ "⊩" ++ (showT sn α) ++ ". " ++ snd ++ ")" , fm Data.Nat.⊔ (suc sm) , fn Data.Nat.⊔ sn }
      }

  open import SOAS.Abstract.ExpStrength
  open CompatStrengths ⅀:CompatStr
  open import SOAS.Metatheory.Semantics {T} [_]_ ⅀F CoalgStr 𝕋:Init

  open Semantics

  PP' : 𝕋 ⇾̣₂ 𝓟𝓟
  PP' = 𝕤𝕖𝕞 𝓟𝓟ᵃ

  𝓢 : Family₂
  𝓢 𝔐 τ Γ = String

  PP : 𝕋 ⇾̣₂ 𝓢
  PP {𝔐}{τ}{Γ} t =
    let (s , _) = PP' t (m , ρ {𝔐} , n , ϱ {Γ}) in (showMCtxBinder ℕ.zero 𝔐 true false) ++ "; " ++ (showCtxBinder ℕ.zero Γ true false) ++ " ⊢ " ++ s ++ " : " ++ showT τ
    where m = mlen 𝔐
          n = len Γ

          ρ : {𝔑 : MCtx}{Ψ : Ctx}{α : T} → Ψ ⊩ α ∈ 𝔑 → ℕ
          ρ {𝔑} ↓ = pred m
          ρ {⁅ Γ' ⊩ₙ τ' ⁆ 𝔑} (↑ 𝔪) = pred (ρ {𝔑} 𝔪)

          ϱ : {Δ : Ctx}{α : T} → ℐ α Δ → ℕ
          ϱ {Δ} new = pred n
          ϱ {β ∙ Δ} (old v) = pred (ϱ {Δ} v)
