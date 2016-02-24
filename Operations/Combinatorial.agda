module Operations.Combinatorial where

open import Data.Bool using (true; false)
import      Data.Bool as B
import      Data.Fin  as F
open import Data.Nat  using (ℕ; suc)
open import Data.Vec  using ([]; _∷_)
import      Data.Vec  as V
open import Relation.Binary.PropositionalEquality

open import Types
open import Eval

not : Closed (𝔹 ⇒ 𝔹)
not = lam (var F.zero refl nand var F.zero refl)

not-prf : ∀ {n} {ctx : Ctx n} {Γ : Env ctx} b → (Γ ⟦ not ⟧) b ≡ B.not b
not-prf true = refl
not-prf false = refl

not⁺ : ∀ n → Closed (𝔹⁺ n ⇒ 𝔹⁺ n)
not⁺ 0 = lam []
not⁺ (suc n) = lam (not ∙ head (var F.zero refl) ∷ not⁺ n ∙ tail (var F.zero refl))

not⁺-prf : ∀ {n m} {ctx : Ctx m} {Γ : Env ctx} bs → (Γ ⟦ not⁺ n ⟧) bs ≡ V.map B.not bs
not⁺-prf [] = refl
not⁺-prf (true ∷ bs) = cong₂ _∷_ refl (not⁺-prf bs)
not⁺-prf (false ∷ bs) = cong₂ _∷_ refl (not⁺-prf bs)


and : Closed (𝔹 ⇒ (𝔹 ⇒ 𝔹))
and = lam (lam (not ∙ ((var (F.suc F.zero) refl) nand (var F.zero refl))))

and-prf : ∀ a b → ([] ⟦ and ⟧) a b ≡ B._∧_ a b
and-prf  true  true = refl
and-prf  true false = refl
and-prf false  true = refl
and-prf false false = refl

and⁺ : ∀ n → Closed (𝔹⁺ n ⇒ (𝔹⁺ n ⇒ 𝔹⁺ n))
and⁺ 0 = lam (lam [])
and⁺ (suc n) = lam (lam (x ∷ xs))
  where
  x  = and    ∙ head (var (F.suc F.zero) refl) ∙ head (var F.zero refl)
  xs = and⁺ n ∙ tail (var (F.suc F.zero) refl) ∙ tail (var F.zero refl)

and⁺-prf : ∀ {n m} {ctx : Ctx m} {Γ : Env ctx} as bs → (Γ ⟦ and⁺ n ⟧) as bs ≡ V.zipWith B._∧_ as bs
and⁺-prf [] [] = refl
and⁺-prf ( true ∷ as) ( true ∷ bs) = cong₂ _∷_ refl (and⁺-prf as bs)
and⁺-prf ( true ∷ as) (false ∷ bs) = cong₂ _∷_ refl (and⁺-prf as bs)
and⁺-prf (false ∷ as) ( true ∷ bs) = cong₂ _∷_ refl (and⁺-prf as bs)
and⁺-prf (false ∷ as) (false ∷ bs) = cong₂ _∷_ refl (and⁺-prf as bs)


or : Closed (𝔹 ⇒ (𝔹 ⇒ 𝔹))
or = lam (lam (l nand r))
  where
  l = ((var (F.suc F.zero) refl) nand (var (F.suc F.zero) refl))
  r = ((var F.zero refl) nand (var F.zero refl))

or-prf : ∀ a b → ([] ⟦ or ⟧) a b ≡ B._∨_ a b
or-prf  true  true = refl
or-prf  true false = refl
or-prf false  true = refl
or-prf false false = refl

or⁺ : ∀ n → Closed (𝔹⁺ n ⇒ (𝔹⁺ n ⇒ 𝔹⁺ n))
or⁺ 0 = lam (lam [])
or⁺ (suc n) = lam (lam (x ∷ xs))
  where
  x  = or    ∙ head (var (F.suc F.zero) refl) ∙ head (var F.zero refl)
  xs = or⁺ n ∙ tail (var (F.suc F.zero) refl) ∙ tail (var F.zero refl)

or⁺-prf : ∀ {n m} {ctx : Ctx m} {Γ : Env ctx} as bs → (Γ ⟦ or⁺ n ⟧) as bs ≡ V.zipWith B._∨_ as bs
or⁺-prf [] [] = refl
or⁺-prf ( true ∷ as) ( true ∷ bs) = cong₂ _∷_ refl (or⁺-prf as bs)
or⁺-prf ( true ∷ as) (false ∷ bs) = cong₂ _∷_ refl (or⁺-prf as bs)
or⁺-prf (false ∷ as) ( true ∷ bs) = cong₂ _∷_ refl (or⁺-prf as bs)
or⁺-prf (false ∷ as) (false ∷ bs) = cong₂ _∷_ refl (or⁺-prf as bs)


xor : Closed (𝔹 ⇒ (𝔹 ⇒ 𝔹))
xor = lam (lam (lam (l nand r) ∙ x))
  where
  x = (var (F.suc F.zero) refl) nand (var F.zero refl)
  l = ((var (F.suc (F.suc F.zero)) refl) nand (var F.zero refl))
  r = ((var F.zero refl) nand (var (F.suc F.zero) refl))

xor-prf : ∀ a b → ([] ⟦ xor ⟧) a b ≡ B._xor_ a b
xor-prf  true  true = refl
xor-prf  true false = refl
xor-prf false  true = refl
xor-prf false false = refl

xor⁺ : ∀ n → Closed (𝔹⁺ n ⇒ (𝔹⁺ n ⇒ 𝔹⁺ n))
xor⁺ 0 = lam (lam [])
xor⁺ (suc n) = lam (lam (x ∷ xs))
  where
  x  = xor    ∙ head (var (F.suc F.zero) refl) ∙ head (var F.zero refl)
  xs = xor⁺ n ∙ tail (var (F.suc F.zero) refl) ∙ tail (var F.zero refl)

xor⁺-prf : ∀ {n m} {ctx : Ctx m} {Γ : Env ctx} as bs → (Γ ⟦ xor⁺ n ⟧) as bs ≡ V.zipWith B._xor_ as bs
xor⁺-prf [] [] = refl
xor⁺-prf ( true ∷ as) ( true ∷ bs) = cong₂ _∷_ refl (xor⁺-prf as bs)
xor⁺-prf ( true ∷ as) (false ∷ bs) = cong₂ _∷_ refl (xor⁺-prf as bs)
xor⁺-prf (false ∷ as) ( true ∷ bs) = cong₂ _∷_ refl (xor⁺-prf as bs)
xor⁺-prf (false ∷ as) (false ∷ bs) = cong₂ _∷_ refl (xor⁺-prf as bs)
