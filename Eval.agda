module Eval where

open import Data.Bool
open import Data.Fin
open import Data.Vec renaming (head to vhead; tail to vtail)
open import Relation.Binary.PropositionalEquality

open import Types

⟦_⟧ᵗ : Type → Set
⟦ 𝔹 ⟧ᵗ = Bool
⟦ 𝔹⁺ n ⟧ᵗ = Vec Bool n
⟦ σ ⇒ τ ⟧ᵗ = ⟦ σ ⟧ᵗ → ⟦ τ ⟧ᵗ

data Env : ∀ {n} → Ctx n → Set where
  [] : Env []
  _∷_ : ∀ {n} {Γ : Ctx n} {τ} → ⟦ τ ⟧ᵗ → Env Γ → Env (τ ∷ Γ)

lookupEnv : ∀ {n} {Γ : Ctx n} (i : Fin n) → Env Γ → ⟦ lookup i Γ ⟧ᵗ
lookupEnv zero (x ∷ env) = x
lookupEnv (suc i) (x ∷ env) = lookupEnv i env

_⟦_⟧ : ∀ {n} {Γ : Ctx n} {τ} → Env Γ → Term Γ τ → ⟦ τ ⟧ᵗ
env ⟦ bitI ⟧ = true
env ⟦ bitO ⟧ = false
env ⟦ []   ⟧ = []
env ⟦ x ∷ xs ⟧ = env ⟦ x ⟧ ∷ env ⟦ xs ⟧
env ⟦ x nand y ⟧ with env ⟦ x ⟧ | env ⟦ y ⟧
env ⟦ x nand y ⟧ |  true |  true = false
env ⟦ x nand y ⟧ |     _ |     _ =  true
env ⟦ head t ⟧ = vhead (env ⟦ t ⟧)
env ⟦ tail t ⟧ = vtail (env ⟦ t ⟧)
env ⟦ var i refl ⟧ = lookupEnv i env
env ⟦ f ∙ x ⟧ = (env ⟦ f ⟧) (env ⟦ x ⟧)
env ⟦ lam σ t ⟧ = λ x → (x ∷ env) ⟦ t ⟧
