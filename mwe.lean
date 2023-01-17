import Std.Data.List.Basic
import Mathlib.Tactic.applyFun
import Mathlib.Data.List.Basic


open Lean


lemma List.getLast?_some {α} {l: List α} {a:α} (h:List.getLast? l = some a): 
  List.getLast l (by have h₂:= congr_arg Option.isSome h; simp at h₂; simp [h₂]) = a := by sorry

lemma examp  (h: List.getLast? l = some e): l ≠ [] := by
  have h₂ := List.getLast?_some h
  generalize_proofs h₂
