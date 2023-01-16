import Std.Data.List.Basic
import Mathlib.Tactic.applyFun

open Lean

def f (x: α): α := sorry

lemma examp  (y:β) (h:  β → (∀ x:α, f x = x)): (λ x:α => f x) = (λ x => x) := by
  simp [h] -- No error message
  simp_rw [h] -- No error message
  rw [h]  -- Can't rewrite under binders