module Check where

open import Data.Fin hiding (fromℕ)
open import Data.Nat
open import Data.Vec hiding (head; tail)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Types
open import Utils

data Check {n} (Γ : Ctx n) : Syntax → Set where
  yes : (τ : Type) (t : Term Γ τ) → Check Γ (erase t)
  no  : {e : Syntax} → Check Γ e

check : ∀ {n} (Γ : Ctx n) (t : Syntax) → Check Γ t
check Γ bitI = yes 𝔹 bitI
check Γ bitO = yes 𝔹 bitO
check Γ [] = yes (𝔹⁺ 0) []
check Γ (x ∷ xs) with check Γ x | check Γ xs
check Γ (.(erase t) ∷ .(erase t₁)) | yes 𝔹 t | yes (𝔹⁺ n) t₁ = yes (𝔹⁺ (suc n)) (t ∷ t₁)
check Γ (x ∷ xs) | _ | _ = no
check Γ (x nand y) with check Γ x | check Γ y
check Γ (._ nand ._) | yes 𝔹 x | yes 𝔹 y = yes 𝔹 (x nand y)
check Γ (_ nand _) | _ | _ = no
check Γ (reg xt ft) with check Γ xt | check Γ ft
check Γ (reg ._ ._) | yes τ xt | yes (τ′ ⇒ (τ″ × σ)) ft with τ ≟T τ′ | τ ≟T τ″
check Γ (reg ._ ._) | yes τ xt | yes (.τ ⇒ (.τ × σ)) ft | yes refl | yes refl = yes _ (reg xt ft)
check Γ (reg ._ ._) | yes τ xt | yes (τ′ ⇒ (τ″ × σ)) ft | _ | _ = no
check Γ (reg _ _) | _ | _ = no
check Γ (pair xt yt) with check Γ xt | check Γ yt
check Γ (pair ._ ._) | yes σ t | yes τ t₁ with σ ≟T τ
check Γ (pair ._ ._) | yes σ t | yes .σ t₁ | yes refl = yes (σ × σ) (pair t t₁)
check Γ (pair ._ ._) | yes σ t | yes τ t₁ | no _ = no
check Γ (pair xt yt) | _ | _ = no
check Γ (latest t) with check Γ t
check Γ (latest ._) | yes (ℂ τ) t′ = yes τ (latest t′)
check Γ (latest t) | _ = no
check Γ (head x) with check Γ x
check Γ (head ._) | yes (𝔹⁺ (suc n)) t = yes 𝔹 (head t)
check Γ (head _) | _ = no
check Γ (tail xs) with check Γ xs
check Γ (tail .(erase t)) | yes (𝔹⁺ (suc n)) t = yes (𝔹⁺ n) (tail t)
check Γ (tail xs) | _ = no
check {n} Γ (var i) with fromℕ n i
check Γ (var ._) | yes m = yes (lookup m Γ) (var m refl)
check Γ (var ._) | no m = no
check Γ (x ∙ y) with check Γ x | check Γ y
check Γ (._ ∙ ._) | yes (σ ⇒ τ) x | yes σ′ y with σ ≟T σ′
check Γ (._ ∙ ._) | yes (σ ⇒ τ) x | yes .σ y | yes refl = yes τ (x ∙ y)
check Γ (._ ∙ ._) | yes (σ ⇒ τ) x | yes σ′ y | no ¬p = no
check Γ (x ∙ y) | _ | _ = no
check Γ (lam τ x) with check (τ ∷ Γ) x
check Γ (lam τ ._) | yes τ₁ t = yes (τ ⇒ τ₁) (lam t)
check Γ (lam τ x) | no = no
