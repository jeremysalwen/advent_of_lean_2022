import Std.Data.List.Basic
import Mathlib.Tactic.applyFun
import Mathlib.Data.List.Basic


open Lean

def f (a:ℕ ): ℕ := sorry 
lemma foo (a:ℕ): f a = 5 :=by sorry
lemma examp :f a + f b = f c + 5 := by
  simp (config := {singlePass := true})  [foo]
