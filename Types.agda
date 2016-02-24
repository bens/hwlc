module Types where

open import Data.Bool
open import Data.Fin
open import Data.Nat renaming (_≟_ to _≟N_)
open import Data.Vec hiding (head; tail)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

infixl 80 _∙_

data Type : Set where
  𝔹  : Type
  𝔹⁺ : ℕ → Type
  _⇒_ : Type → Type → Type

data Syntax : Set where
  bitI   : Syntax
  bitO   : Syntax
  []     : Syntax
  _∷_    : Syntax → Syntax → Syntax
  _nand_ : Syntax → Syntax → Syntax
  head   : Syntax → Syntax
  tail   : Syntax → Syntax
  var    : ℕ → Syntax
  _∙_    : Syntax → Syntax → Syntax
  lam    : Type → Syntax → Syntax

Ctx : ℕ → Set
Ctx = Vec Type

data Term {n} (Γ : Ctx n) : Type → Set where
  bitI   : Term Γ 𝔹
  bitO   : Term Γ 𝔹
  []     : Term Γ (𝔹⁺ 0)
  _∷_    : ∀ {n} → Term Γ 𝔹 → Term Γ (𝔹⁺ n) → Term Γ (𝔹⁺ (suc n))
  _nand_ : Term Γ 𝔹 → Term Γ 𝔹 → Term Γ 𝔹
  head   : ∀ {n} → Term Γ (𝔹⁺ (suc n)) → Term Γ 𝔹
  tail   : ∀ {n} → Term Γ (𝔹⁺ (suc n)) → Term Γ (𝔹⁺ n)
  var    : ∀ {τ} (i : Fin n) → (lookup i Γ ≡ τ) → Term Γ τ
  _∙_    : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam    : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

≡𝔹⁺ : ∀ {n m} → 𝔹⁺ n ≡ 𝔹⁺ m → n ≡ m
≡𝔹⁺ refl = refl

≡⇒₁ : ∀ {σ σ′ τ τ′} → σ ⇒ τ ≡ σ′ ⇒ τ′ → σ ≡ σ′
≡⇒₁ refl = refl

≡⇒₂ : ∀ {σ σ′ τ τ′} → σ ⇒ τ ≡ σ′ ⇒ τ′ → τ ≡ τ′
≡⇒₂ refl = refl

_≟T_ : (σ τ : Type) → Dec (σ ≡ τ)
𝔹 ≟T 𝔹 = yes refl
𝔹 ≟T 𝔹⁺ _ = no (λ ())
𝔹 ≟T (_ ⇒ _) = no (λ ())
𝔹⁺ _ ≟T 𝔹 = no (λ ())
𝔹⁺ n ≟T 𝔹⁺ m with n ≟N m
𝔹⁺ n ≟T 𝔹⁺ .n | yes refl = yes refl
𝔹⁺ n ≟T 𝔹⁺ m  | no ¬p = no (λ x → ¬p (≡𝔹⁺ x))
𝔹⁺ x ≟T (y ⇒ y₁) = no (λ ())
(_ ⇒ _) ≟T 𝔹 = no (λ ())
(σ ⇒ τ) ≟T 𝔹⁺ x₂ = no (λ ())
(σ ⇒ τ) ≟T (σ₁ ⇒ τ₁) with σ ≟T σ₁ | τ ≟T τ₁
(σ ⇒ τ) ≟T (σ₁ ⇒ τ₁) | yes p | yes p₁ = yes (cong₂ _⇒_ p p₁)
(σ ⇒ τ) ≟T (σ₁ ⇒ τ₁) |     _ | no  ¬p = no (λ x → ¬p (≡⇒₂ x))
(σ ⇒ τ) ≟T (σ₁ ⇒ τ₁) | no ¬p |      _ = no (λ x → ¬p (≡⇒₁ x))

erase : ∀ {n} {Γ : Ctx n} {τ} → Term Γ τ → Syntax
erase bitI       = bitI
erase bitO       = bitO
erase []         = []
erase (x ∷ xs)   = erase x ∷ erase xs
erase (x nand y) = erase x nand erase y
erase (head x)   = head (erase x)
erase (tail x)   = tail (erase x)
erase (var v _)  = var (toℕ v)
erase (t ∙ u)    = erase t ∙ erase u
erase (lam σ t)  = lam σ (erase t)
