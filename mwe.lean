import Mathlib.Tactic.LibrarySearch
import Lean

theorem Nat.toDigitsCore_slow (b:ℕ) (n:ℕ) (P: b>1): ∀i:ℕ, (Nat.toDigits b n).reverse.getD (i+1) '0' = (Nat.toDigits b (n/b)).reverse.getD i '0':= by
  intro i

  conv =>
    left
    unfold toDigits toDigitsCore
  sorry


theorem Nat.toDigitsCore_fast (b:ℕ) (n:ℕ) (P: b>1): ∀i:ℕ, (Nat.toDigits b n).reverse.getD (i+1) '0' = (Nat.toDigits b (n/b)).reverse.getD i '0':= by
  intro i

  rw [toDigits, toDigitsCore]
  sorry