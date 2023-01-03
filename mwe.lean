import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


def fn (b n:ℕ): List ℕ  := sorry

theorem demo (b n i:ℕ) (h: i< List.length (fn b n)) :
    List.length (fn b n) - 1 - (List.length (fn b n) - 1 - i) = i :=
    Nat.sub_sub_self (Nat.le_sub_of_add_le h)

