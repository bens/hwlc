module Eval where

open import Coinduction
open import Data.Bool
open import Data.Fin
open import Data.Product using (Σ; _,_)
import      Data.Product as P
open import Data.Stream using (Stream; _∷_)
import      Data.Stream as S
open import Data.Vec    using (Vec; []; _∷_)
import      Data.Vec    as V
open import Relation.Binary.PropositionalEquality

open import Types

⟦_⟧ᵗ : Type → Set
⟦ 𝔹     ⟧ᵗ = Bool
⟦ 𝔹⁺ n  ⟧ᵗ = Vec Bool n
⟦ ℂ τ   ⟧ᵗ = Stream ⟦ τ ⟧ᵗ
⟦ σ ⇒ τ ⟧ᵗ = ⟦ σ ⟧ᵗ → ⟦ τ ⟧ᵗ
⟦ σ × τ ⟧ᵗ = P._×_ ⟦ σ ⟧ᵗ ⟦ τ ⟧ᵗ

data Env : ∀ {n} → Ctx n → Set where
  [] : Env []
  _∷_ : ∀ {n} {Γ : Ctx n} {τ} → ⟦ τ ⟧ᵗ → Env Γ → Env (τ ∷ Γ)

lookupEnv : ∀ {n} {Γ : Ctx n} (i : Fin n) → Env Γ → ⟦ V.lookup i Γ ⟧ᵗ
lookupEnv zero (x ∷ env) = x
lookupEnv (suc i) (x ∷ env) = lookupEnv i env

private
  runReg : ∀ {σ τ} → (⟦ τ ⟧ᵗ → P._×_ ⟦ τ ⟧ᵗ ⟦ σ ⟧ᵗ) → ⟦ τ ⟧ᵗ → Stream ⟦ σ ⟧ᵗ
  runReg f s with f s
  runReg f s | s′ , x = x ∷ ♯ (runReg f s′)

_⟦_⟧ : ∀ {n} {Γ : Ctx n} {τ} → Env Γ → Term Γ τ → ⟦ τ ⟧ᵗ
env ⟦ bitI ⟧ = true
env ⟦ bitO ⟧ = false
env ⟦ [] ⟧ = []
env ⟦ x ∷ xs ⟧ = env ⟦ x ⟧ ∷ env ⟦ xs ⟧
env ⟦ x nand y ⟧ with env ⟦ x ⟧ | env ⟦ y ⟧
env ⟦ x nand y ⟧ |  true |  true = false
env ⟦ x nand y ⟧ |     _ |     _ =  true
env ⟦ reg xt ft ⟧ = runReg (env ⟦ ft ⟧) (env ⟦ xt ⟧)
env ⟦ pair xt yt ⟧ = (env ⟦ xt ⟧) , (env ⟦ yt ⟧)
env ⟦ latest t ⟧ = S.head (env ⟦ t ⟧)
env ⟦ head t ⟧ = V.head (env ⟦ t ⟧)
env ⟦ tail t ⟧ = V.tail (env ⟦ t ⟧)
env ⟦ var i refl ⟧ = lookupEnv i env
env ⟦ f ∙ x ⟧ = (env ⟦ f ⟧) (env ⟦ x ⟧)
env ⟦ lam t ⟧ = λ x → (x ∷ env) ⟦ t ⟧
