module Utils where

open import Data.Fin using (Fin)
import      Data.Fin as F
open import Data.Nat

data Fromℕ (n : ℕ) : ℕ → Set where
  yes : (m : Fin n) → Fromℕ n (F.toℕ m)
  no  : (m : ℕ)     → Fromℕ n (n + m)

fromℕ : ∀ n m → Fromℕ n m
fromℕ zero m = no m
fromℕ (suc n) zero = yes F.zero
fromℕ (suc n) (suc m) with fromℕ n m
fromℕ (suc n) (suc .(F.toℕ m)) | yes m = yes (F.suc m)
fromℕ (suc n) (suc .(n + m))   | no  m = no m
