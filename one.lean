import Lean
import Mathlib.Tactic.Find
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.applyFun
import Init.Data.String.Basic
import Init.Data.Int.Basic
import Std.Data.Array.Init.Lemmas
import Std.Data.Array.Lemmas
import Std.Data.List.Init.Lemmas
import Std.Data.Nat.Lemmas
import Std.Data.Int.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SolveByElim
import Mathlib.Data.List.MinMax
import Aesop



open Lean Parsec


set_option profiler true

lemma Array.ext_iff {α : Type u_1} {as bs : Array α} :  as = bs ↔ as.data = bs.data := by
  apply Iff.intro
  . intro eq
    simp only [eq]
  . intro eq
    exact Array.ext' eq
  
@[simp]
lemma List.modifyLast_singleton (f: α → α) (a: α): List.modifyLast f [a] = [f a] := by
  rw [← nil_append [a], modifyLast_append_one, nil_append]



def String.toNatAux (s: List Char) (accum:ℕ): ℕ :=
  match s with
  | [] => accum
  | head::tail =>  String.toNatAux tail (accum * 10 + (head.toNat - '0'.toNat))

def String.toNatΔ (s: List Char): ℕ :=
    String.toNatAux s 0

lemma String.toNatAux_accumulates (s: List Char) (accum:ℕ): 
  String.toNatAux s accum = String.toNatAux s 0 + accum * 10^(List.length s) := by
  induction s generalizing accum with
  | nil => unfold toNatAux; simp
  | cons head tail ih =>
    unfold toNatAux
    rw [ih]
    conv => right; rw [ih]
    simp [Nat.succ_eq_add_one]
    ring


theorem String.toNatΔ_cons (head: Char) (tail: List Char): 
  String.toNatΔ (head::tail) = (head.toNat - '0'.toNat)*10^(List.length tail) + (String.toNatΔ tail) := by
  unfold String.toNatΔ
  rw [String.toNatAux, String.toNatAux_accumulates]
  ring

def String.toIntΔ (s: List Char): ℤ :=
  match s with
  | [] => 0
  | h::tail => if h = '-' then - String.toNatΔ tail else String.toNatΔ (h::tail)

def Int.reprΔ (i: ℤ): List Char :=
  match i with
  | Int.ofNat m => Nat.toDigits 10 m
  | Int.negSucc m => ['-'] ++ Nat.toDigits 10 (Nat.succ m)




theorem Nat.toDigitsCore_ne_nil (P: f > n): Nat.toDigitsCore b f n a ≠ [] := by
  unfold Nat.toDigitsCore
  split
  . case _ => contradiction
  . case _ _ _ _ fuel =>
    simp
    have h: ∀x, List.length (Nat.toDigitsCore b fuel (n / b) (x :: a)) ≠ 0 := by
      simp [Nat.to_digits_core_lens_eq]
    split
    case _ => simp
    case _ => 
      intro P₂
      apply h
      rw [P₂]
      simp

lemma Nat.toDigits_ne_nil: Nat.toDigits b n ≠ [] := by
  unfold Nat.toDigits
  simp [Nat.toDigitsCore_ne_nil]

lemma Int.reprΔ_ne_nil (i: ℤ): Int.reprΔ i ≠ [] := by
  unfold Int.reprΔ
  cases i with
  | ofNat m => simp only; apply Nat.toDigits_ne_nil
  | negSucc m => simp only [List.singleton_append, ne_eq, not_false_iff]


@[simp]
lemma Nat.digitChar_is_digit (n: ℕ) (P: n < 10): Char.isDigit (Nat.digitChar n) = true := by
  revert n
  decide

lemma Nat.toDigitsCore_digits (b: ℕ) (n:ℕ) (P: b <= 10) (Q: b > 1): c ∈ (Nat.toDigitsCore b f n a) → (c.isDigit ∨ c ∈ a):= by
  induction n using Nat.strong_induction_on generalizing f a with
  | _ n h =>
    have _: b>0 := by calc
            b > 1 := Q
            _ > 0 := by simp
    have nmodb_le10: n % b < 10 := by calc
      n % b < b  := by apply Nat.mod_lt;  simp [*]
      _     ≤ 10 := by exact P
    unfold Nat.toDigitsCore
    split
    next =>
      intro h₂
      simp [h₂]
    next _ _ _ fuel=>
      simp
      intro h₂
      cases h₃: n / b == 0 with
      | true =>
        have h₄:n/b = 0 := by apply LawfulBEq.eq_of_beq; assumption
        simp [h₄] at h₂
        cases h₂ with
        | inr h₅ => simp [h₅]
        | inl h₅ =>
          left 
          rw [h₅]
          simp [nmodb_le10, Nat.digitChar_is_digit]
      | false =>
        have h₄: n/b ≠ 0 := by apply ne_of_beq_false; assumption
        simp [h₄] at h₂
        have h₅: Char.isDigit c = true ∨ c ∈ Nat.digitChar (n % b) :: a := by
          apply h (n/b) (f:= fuel) (a:=(Nat.digitChar (n % b) :: a))
          next =>
            have h₅: n ≠ 0 := by 
              intro x
              unfold Ne at h₄
              have h₆:= Nat.zero_div b
              conv at h₆ =>
                left
                rw [← x]
              contradiction
            apply Nat.div_lt_self
            . simp [h₅, Nat.pos_of_ne_zero]
            . simp [Q]
          next _ => exact h₂
        simp at h₅
        cases h₅ with
        | inl h₆ => simp [h₆]
        | inr h₆ => cases h₆ with
          | inl h₇ => rw [h₇]; left; simp [nmodb_le10, Nat.digitChar_is_digit]
          | inr h₇ => simp [h₇]


lemma Nat.toDigitsCore_accumulates: toDigitsCore b f n (start ++ rest) = toDigitsCore b f n start ++ rest := by
  induction f using Nat.strong_induction_on generalizing start rest n with
  | h f ih => 
    unfold  toDigitsCore
    split
    . case h.h_1 => simp
    . case h.h_2 f _ _ _ q =>
      simp
      split
      . case inl =>
        simp
      . case inr =>
        rewrite [← List.cons_append]
        rewrite [ih]
        . rfl
        . simp only [lt_succ_self]

lemma Nat.todigitsCore_accumulates_suffix: toDigitsCore b f n rest = toDigitsCore b f n [] ++ rest := by
  have h: rest = [] ++ rest := by simp
  conv=> left; rw [h]
  apply Nat.toDigitsCore_accumulates

lemma Nat.toDigitsCore_fuel_irrelevant (P: f >= n+1) (Q: b > 1): toDigitsCore b f n rest =  toDigitsCore b (n+1) n rest := by
  induction f using Nat.strong_induction_on generalizing rest n
  case h f ih =>
    unfold toDigitsCore
    simp
    split
    case h_1 =>
      simp at P
    case h_2 n' =>
      conv =>
        left; rw [Nat.todigitsCore_accumulates_suffix]
      conv =>
        right; rw [Nat.todigitsCore_accumulates_suffix]
      split
      case inl =>
        rfl
      case inr =>
        simp
        rw [ih]
        .  cases h: n == (n / b) + 1 with
            | false => 
              simp at h
              rw [← Nat.toDigits, ih, ← Nat.toDigits]
              . calc
                  succ n' ≥  n + 1 := P
                  _ > n := by simp only [gt_iff_lt, lt_add_iff_pos_right]
              . simp [h]
                have h₂: n ≥  n / b + 1 := by 
                  simp
                  apply Nat.div_lt_self
                  . apply Nat.pos_of_ne_zero; intro h; simp only [gt_iff_lt, h, Nat.zero_div, not_true] at *
                  . exact Q
                simp [ge_iff_le] at h₂
                have h₃:= Nat.eq_or_lt_of_le h₂
                cases h₃ with
                | inl h₄ => exfalso; apply h; simp only [h₄]
                | inr h₄ => exact h₂
            | true => 
              simp at h
              rw [← h]
        . simp
        . simp [Nat.succ_eq_add_one] at P 
          calc
            n' ≥  n        := P
            n ≥ n / b + 1 := by simp only [add_lt_add_iff_right]; apply Nat.div_lt_self; apply Nat.pos_of_ne_zero; intro h; simp only [gt_iff_lt, h, Nat.zero_div, not_true] at *; apply Q


lemma Nat.toDigits_digits (b: ℕ) (n:ℕ) (P: b <= 10) (Q: b > 1): List.all (Nat.toDigits b n) (Char.isDigit) == true := by
  let h:  ∀ c, c ∈ Nat.toDigitsCore b (n+1) n [] → Char.isDigit c = true ∨ c ∈ [] := by
    intro c
    apply Nat.toDigitsCore_digits  _ _ P Q 
  simp
  simp at h
  unfold Nat.toDigits
  apply h

lemma List.get?_cons {h: α} {tail : List α} {n : Nat} (hn: n>0): (h::tail).get? n = tail.get? (n-1) := by
  conv => left; unfold List.get?
  cases n with
  | zero => simp only at hn
  | succ n => simp only [ge_iff_le, Nat.succ_sub_succ_eq_sub, nonpos_iff_eq_zero, tsub_zero]


theorem Nat.toDigitsCore_shift' (b:ℕ) (n:ℕ) (P: b>1): ∀i:ℕ, (Nat.toDigits b n).reverse.getD (i+1) '0' = (Nat.toDigits b (n/b)).reverse.getD i '0':= by
  intro i
  
  rw [toDigits, toDigitsCore]

  simp only [add_eq, add_zero]
  split
  . next heq =>
    conv => left; unfold List.getD
    simp only [List.get?, Option.getD_none]
    rw [heq]
    unfold toDigits toDigitsCore digitChar
    simp only [Nat.zero_div, zero_mod, zero_ne_one, ite_false, ite_true, List.reverse_cons, List.reverse_nil,
  List.nil_append, List.getD_singleton_default_eq]
    
  . next heq =>
    rw [Nat.todigitsCore_accumulates_suffix]
    rw [List.getD, List.getD]
    congr 1
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.cons.injEq, succ.injEq, and_imp, forall_apply_eq_imp_iff₂, forall_apply_eq_imp_iff', forall_eq', 
      List.get?, add_eq, add_zero]
    rw [Nat.toDigitsCore_fuel_irrelevant, ← Nat.toDigits]
    . simp only [ge_iff_le]
      have h: n ≠ 0 := by 
        simp only [ne_eq]
        intro h
        rw [h] at heq
        simp only [Nat.zero_div] at heq
      apply Nat.div_lt_self
      . simp only [ne_eq, h, not_false_iff, Nat.pos_of_ne_zero]
      . exact P
    . exact P
    
theorem Nat.toDigitsCore_shift (b:ℕ) (n:ℕ) (P: b>1): ∀i:ℕ, i>0 → (Nat.toDigits b n).reverse.getD i '0' = (Nat.toDigits b (n/b)).reverse.getD (i-1) '0':= by
  intro i igt
  generalize h: i - 1 = p
  have heq: i = p + 1 := by cases i with | zero => contradiction | succ n => simp at h; rw [h]
  rw [heq]
  apply Nat.toDigitsCore_shift'
  exact P

lemma Nat.toDigitsCore_shift_full (b:ℕ) (n:ℕ) (P: b>1): ∀i:ℕ, (Nat.toDigits b n).reverse.getD i '0' = (Nat.toDigits b (n/b^i)).reverse.getD 0 '0' := by
  intro i
  induction i generalizing n with
  | zero =>
    simp only [zero_eq, pow_zero, Nat.div_one]
  | succ i ih =>
    rw [Nat.toDigitsCore_shift]
    . simp
      rw [ih]
      congr 3
      rw [Nat.div_div_eq_div_mul]
      congr 1
      rw [Nat.pow_succ']
    . exact P
    . simp

def Nat.digit (base:ℕ) (n:ℕ) (index:ℕ): ℕ := (n / base^index) % base

@[simp]
theorem Nat.digit_lt_base {base n index: ℕ} (P: base > 0): Nat.digit base n index < base := by
  unfold Nat.digit
  apply Nat.mod_lt _ P



theorem Nat.toDigits_eq_digit_rev (b: ℕ) (n:ℕ) (P: b > 1): 
 ∀ i:ℕ, (Nat.toDigits b n).reverse.getD i '0' = Nat.digitChar (Nat.digit b n i) := by
  intro i
  rw [Nat.toDigitsCore_shift_full]
  . unfold toDigits toDigitsCore digit
    simp only [add_eq, add_zero]
    split
    . next heq =>
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.getD._eq_1, List.get?, Option.getD_some]
    . next heq =>
      rw [Nat.todigitsCore_accumulates_suffix]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
  List.getD._eq_1, List.get?, Option.getD_some]
  . exact P

theorem Nat.toDigitsCore_length_eq_log  (b fuel n: ℕ ) (P: b>1) (R: fuel>n): List.length (Nat.toDigitsCore b fuel n accum) = Nat.log b n + 1 + List.length accum:= by
  have heq: accum = [] ++ accum := by  simp only [List.nil_append]
  rw [heq, Nat.toDigitsCore_accumulates]
  simp only [List.length_append, List.nil_append, add_left_inj]
  induction n using Nat.strong_induction_on generalizing fuel accum
  case h n ih =>
    unfold toDigitsCore
    split
    . next i _ _ _=> 
      exfalso
      apply Nat.not_lt_of_le (Nat.zero_le i)
      apply R
    . next  w y p l =>
      simp; split
      . next i h₂=>
        simp
        left
        have  h: b > 0 := pos_of_gt P
        apply (Nat.div_lt_one_iff h).1
        simp only [h₂, zero_lt_one]
      . next n heq =>
        rw [Nat.todigitsCore_accumulates_suffix]
        simp only [List.length_append, List.length_singleton, add_left_inj]
        have h: n/b<n := by
          apply Nat.div_lt_self
          . apply Nat.pos_of_ne_zero
            intro h
            simp only [h, Nat.zero_div, not_true] at heq
          . apply P
        rw [ih]
        . rw [Nat.log_div_base, Nat.sub_add_cancel]
          apply Nat.log_pos
          . apply P
          . apply (Nat.one_le_div_iff (Nat.lt_of_succ_lt P)).1
            apply Nat.succ_le_iff.2
            apply Nat.pos_of_ne_zero
            apply heq
        . exact h
        . exact []
        . calc
          l ≥ n := by exact le_of_lt_succ R
          _ > n/b := h
        . simp

lemma Nat.toDigits_length_eq_log  {b n: ℕ} (P: b>1): List.length (Nat.toDigits b n) = Nat.log b n + 1:= by
  unfold Nat.toDigits
  rw [Nat.toDigitsCore_length_eq_log]
  . simp only [List.length_nil, add_zero]
  . exact P
  . apply Nat.lt_succ_self
  

theorem Nat.toDigits_eq_digit (b n:ℕ) (P: b>1):
 ∀ i:ℕ, i < List.length (Nat.toDigits b n) →  List.getD (Nat.toDigits b n) i '0' = Nat.digitChar (Nat.digit b n (List.length (Nat.toDigits b n) - 1 - i)) := by
  intro i h
  rw [← Nat.toDigits_eq_digit_rev b n P (List.length (Nat.toDigits b n) - 1 - i)]
  rw [ List.getD, List.getD, List.get?_reverse]
  congr
  . have h₂: List.length (toDigits b n) - 1 ≥ (List.length (toDigits b n) - 1 - i) := by simp
    have h₃: List.length (toDigits b n) ≥ 1 := by calc 
      List.length (toDigits b n) > i := h
      _ ≥ 0 := by simp only [ge_iff_le, _root_.zero_le]
    have h₄: i ≤ List.length (toDigits b n) - 1 := by apply Nat.le_pred_of_lt; exact h
    zify [h₂, h₃, h₄]
    apply Int.eq_of_sub_eq_zero
    ring_nf
  . rw [Nat.sub_sub]
    apply Nat.sub_lt_self
    . simp only [add_pos_iff, true_or]
    . rw [Nat.add_comm]
      apply Nat.lt_iff_add_one_le.1 h

theorem Nat.digit_gt_log_eq_zero (b n i:ℕ) (P: b>1) (Q: i > Nat.log b n ): Nat.digit b n i = 0 := by
  unfold digit
  convert Nat.zero_mod b
  apply Nat.div_eq_of_lt
  apply Nat.lt_pow_of_log_lt
  . exact P
  . exact Q

def List.lastN (n:ℕ) (l:List α): List α := List.drop (l.length-n) l

@[simp]
theorem List.lastN_zero (l:List α): List.lastN 0 l = [] := by
  unfold List.lastN
  simp

@[simp]
theorem List.lastN_length_eq_self (l: List α): List.lastN (length l) l = l := by
  unfold List.lastN
  simp

@[simp]
lemma List.lastN_length (l: List α) (i:ℕ): length (List.lastN i l) = min i (length l) := by
  unfold lastN
  simp only [ge_iff_le, length_drop]
  cases h: decide (i ≤  length l) with
  | true => 
    simp at h
    rw [Nat.sub_sub_self h, Nat.min_eq_left h]
  | false =>
    simp at h
    have h₂: length l ≤ i := Nat.le_of_lt h
    simp [h₂]
  
lemma List.lastN_cons (head: α) (tail: List α) (i: ℕ): List.lastN i (head::tail) = if (head::tail).length > i then lastN i tail else head::tail := by
  unfold lastN
  induction tail with
  | nil => 
    split
    case inl heq => simp_all
    case inr heq => 
      simp only [length_singleton, gt_iff_lt, Nat.lt_one_iff, ← ne_eq] at heq
      simp only [length_singleton, ge_iff_le, Nat.sub_eq_zero_of_le (Nat.succ_le_of_lt (Nat.pos_of_ne_zero heq)), drop]
  | cons mid tail _ih=>
    split
    case inl heq =>
      simp [Nat.succ_eq_one_add]
      rw [Nat.add_sub_assoc, ←Nat.succ_eq_one_add, drop._eq_3]
      simp_all only [Nat.le_of_lt_succ, length_cons, Nat.succ_eq_one_add, ge_iff_le, gt_iff_lt]
    case inr heq =>
      simp only [length_cons, gt_iff_lt, not_lt] at heq
      simp only [length_cons, ge_iff_le, Nat.sub_eq_zero_of_le heq, drop]


@[simp]
lemma List.lastN_ge_length (l: List α) (h: n ≥ length l): List.lastN n l = l := by
  unfold List.lastN
  simp [h]

lemma List.lastN_one_eq_getLast (l:List α): l.lastN 1 = l.getLast?.toList:= by
  induction l with
  | nil => simp only [length_nil, ge_iff_le, lastN_ge_length, getLast?_nil, Option.to_list_none]
  | cons head tail ih=> 
    rw [lastN_cons]
    simp only [length_cons, gt_iff_lt, ge_iff_le]
    split
    case inl heq =>
      have hne: tail ≠ [] := by
        apply List.ne_nil_of_length_pos
        apply Nat.succ_lt_succ_iff.1 heq
      rw [getLast?_cons, ih, getLast?_eq_getLast _ hne, List.getLastD]
      split
      . contradiction
      . simp
    case inr heq =>
      simp at heq
      have hnil: tail = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ heq))
      subst tail
      simp only [getLast?_singleton, Option.to_list_some]

lemma List.getLast?_some {α} {l: List α} {a:α} (h:List.getLast? l = some a): 
  List.getLast l (by have h₂:= congr_arg Option.isSome h; simp at h₂; simp [h₂]) = a := by
  have h₂:= congr_arg Option.isSome h
  simp only [Option.isSome_some, getLast?_isSome, ne_eq] at h₂
  rw [ List.getLast?_eq_getLast l h₂] at h
  simp_all only [Option.some.injEq]

lemma List.getLastD_ne_nil (h: l ≠ []): List.getLastD l a = List.getLast l h := by
  cases l with
  | nil => contradiction
  | cons hd tl =>
    rw [List.getLastD_cons, List.getLast_eq_getLastD]

@[simp]
lemma List.get_zero_cons_tail (l:List α) (h: 0 < l.length): List.get l {val:=0, isLt:=h} :: List.tail l = l := by
  cases l with
  | nil => simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, length_nil, lt_self_iff_false] at h
  | cons => simp only [get, tail_cons]

@[simp]
theorem List.lastN_eq_cons_lastN (n) (l:List α) (P:n < l.length): 
get l ⟨ l.length - 1 - n, Nat.sub_one_sub_lt P⟩::(List.lastN n l) = List.lastN (n+1) l := by
  unfold lastN
  have h:  length l - (n + 1) < length l := by
    apply Nat.sub_lt_self
    . simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, add_pos_iff, or_true]
    . simp only [Nat.succ_eq_add_one, P, Nat.succ_le_of_lt]

  conv => 
    right
    rw [List.drop_eq_get_cons  (h:=h)]

  congr 2
  . congr 1
    rw [Nat.sub_sub, Nat.add_comm]
  . rw [← Nat.sub_sub, Nat.sub_add_cancel]
    apply Nat.le_of_add_le_add_right (b:=n)
    rw [Nat.sub_add_cancel]
    . rw [Nat.add_comm, ← Nat.succ_eq_add_one]
      apply Nat.succ_le_of_lt P
    . simp only [P, Nat.le_of_lt]

@[simp]
theorem List.drop_cons (n) (head:α) (tail:List α): List.drop (n+1) (head::tail) = List.drop n tail := by
  simp only [drop, zero_le, ge_iff_le, nonpos_iff_eq_zero, Nat.add_eq, add_zero]

theorem List.lastN_eq_reverse_take (n:ℕ) (l: List α): List.lastN n l = (List.take n l.reverse).reverse := by
  unfold List.lastN
  induction l generalizing n with
  | nil => simp only [length_nil, zero_le, ge_iff_le, nonpos_iff_eq_zero, Nat.zero_sub, tsub_eq_zero_of_le, drop_nil,
  reverse_nil, take_nil]
  | cons head tail ih =>
    simp only [length_cons, tsub_le_iff_right, ge_iff_le, reverse_cons, length_reverse]
    cases h: decide (n ≤ length tail) with
    | false => 
      simp only [decide_eq_false_iff_not, not_le] at h
      rw [Nat.succ_eq_add_one, Nat.add_comm]
      rw [List.take_length_le, List.reverse_append, List.reverse_reverse]
      simp only [tsub_le_iff_right, ge_iff_le, reverse_cons, reverse_nil, nil_append, singleton_append]
      have heq : 1 + length tail - n = 0 := by 
        simp only [tsub_le_iff_right, ge_iff_le, zero_le, nonpos_iff_eq_zero, tsub_eq_zero_iff_le]
        rw [Nat.add_comm]
        apply Nat.le_of_lt_succ
        rw [Nat.succ_eq_add_one]
        simp only [add_lt_add_iff_right, h]
      rw [heq]
      simp only [drop]
      rw [List.length_append, List.length_reverse]
      simp only [length_singleton]
      exact h
    | true =>
      simp only [decide_eq_true_eq] at h
      rw [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_sub_assoc, Nat.add_comm, List.drop_cons, ih]
      congr 1
      rw [List.take_append_of_le_length]
      . simp only [length_reverse]; apply h
      . apply h

@[simp]
theorem Nat.digitChar_sub_zero_eq_self (n:ℕ) (P: n<10): Char.toNat (Nat.digitChar n) - Char.toNat '0' = n := by
  revert n
  decide
theorem Nat.sub_self_sub_eq_min (n k:ℕ): n - (n-k) = Nat.min n k := by
  conv => left; right; rw [Nat.sub_eq_sub_min]
  rw [Nat.sub_sub_self]
  simp only [min_le_iff, ge_iff_le, le_refl, true_or]


@[simp]
theorem List.lastN_eq_tail (l: List α): List.lastN (List.length l - 1) l = List.tail l := by
  unfold List.lastN
  rw [Nat.sub_self_sub_eq_min]
  cases l with
  | nil => simp only [drop, tail_nil]
  | cons hd tl => 
    have h: Nat.succ (List.length tl) ≥ 1 := by 
      apply Nat.succ_le_succ
      apply Nat.zero_le
    simp only [length_cons, Nat.min_eq_right h, ge_iff_le, drop, tail_cons]



@[simp]
lemma Nat.toDigits_zero (b:ℕ): Nat.toDigits b 0 = ['0'] := by
  unfold toDigits toDigitsCore
  simp only [_root_.zero_le, ge_iff_le, nonpos_iff_eq_zero, Nat.zero_div, zero_mod, ite_true, List.cons.injEq]

lemma Nat.toDigits_modulo (b n p i:ℕ) (P: i<p) (Q: b>1): 
    List.getD (List.reverse (Nat.toDigits b (n % b^p))) i '0' = List.getD (List.reverse (Nat.toDigits b n)) i '0' := by
  rw [Nat.toDigits_eq_digit_rev, Nat.toDigits_eq_digit_rev]
  case P => exact Q
  case P => exact Q
  congr 1
  unfold digit
  have hpeq := Nat.sub_add_cancel (le_of_lt P)
  conv => left; left; left; rw [← hpeq, pow_add]
  
  rw [Nat.mod_mul_left_div_self, Nat.mod_mod_of_dvd]
  apply dvd_pow
  . apply dvd_refl
  . simp only [min_le_iff, ge_iff_le, tsub_le_iff_right, le_min_iff, _root_.zero_le, nonpos_iff_eq_zero, ne_eq,
      tsub_eq_zero_iff_le, not_and, not_le, P, implies_true]

lemma List.getD_ext (P: List.length a = List.length b) (Q: ∀ i, List.getD a i d = List.getD b i d): a = b := by
  apply List.ext
  intro n
  have h:= Q n
  unfold getD at h
  cases hlt: decide (n < List.length a) with
  | true => 
    simp only [decide_eq_true_eq] at hlt
    have hltb: n < length b := by rw [← P]; exact hlt
    simp_all only [zero_le, ge_iff_le, nonpos_iff_eq_zero, hltb, get?_eq_get, Option.getD_some, gt_iff_lt, P] 
  | false =>
     simp only [decide_eq_false_iff_not, not_lt] at hlt
     have hltb: n ≥ length b := by rw [← P]; exact hlt
     simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, hlt, List.get?_eq_none.2, hltb]

lemma List.getD_reverse (P: i < List.length l): List.getD (List.reverse l) i d = l[(List.length l - 1 - i)]'(Nat.sub_one_sub_lt P) := by
  unfold List.getD
  rw [List.get?_reverse, List.get?_eq_get]
  simp only [tsub_le_iff_right, ge_iff_le, Option.getD_some, getElem_eq_get]
  . exact Nat.sub_one_sub_lt P
  . exact P


lemma String.toNatΔ_eq_of_rev_get_eq_aux (P: ∀ i, List.getD a.reverse i '0' = List.getD b.reverse i '0') (Q: List.length a ≤ List.length b): String.toNatΔ a = String.toNatΔ b := by
    induction b with
    | nil =>
      simp only [List.length_nil, zero_le, ge_iff_le, nonpos_iff_eq_zero, List.length_eq_zero] at Q
      simp only [Q]
    | cons hd tl ih =>
      cases heq: decide (List.length a = List.length (hd::tl))
      case true => 
        simp only [decide_eq_true_eq] at heq
        have h: a = (hd::tl) := by 
          apply List.getD_ext heq (d:='0')
          intro n
          cases hlt: decide (n < List.length a) with
          | true => 
            simp only [decide_eq_true_eq] at hlt
            have hblt: n < List.length (hd::tl) := by simp_all only [tsub_le_iff_right, ge_iff_le, zero_le, nonpos_iff_eq_zero, tsub_eq_zero_iff_le, heq]
            simp only [gt_iff_lt, hlt, List.getD_eq_get, List.getElem_eq_get, hblt]
            have Q:= P (List.length a -1 - n)
            conv at Q => right; rw [heq]
            rw [ List.getD_reverse (Nat.sub_one_sub_lt hlt),
              List.getD_reverse (Nat.sub_one_sub_lt hblt)] at Q
            simp only [tsub_le_iff_right, ge_iff_le, Nat.sub_sub_self (Nat.le_pred_of_lt hlt), List.getElem_eq_get,
              Nat.sub_sub_self (Nat.le_pred_of_lt hblt)] at Q
            apply Q
            
          | false => 
            simp only [decide_eq_false_iff_not, not_lt] at hlt
            have hblt: n ≥ List.length (hd::tl) := by simp_all only [tsub_le_iff_right, ge_iff_le, zero_le, nonpos_iff_eq_zero, tsub_eq_zero_iff_le, heq]
            simp only [List.getD_eq_get?, zero_le, ge_iff_le, nonpos_iff_eq_zero, hlt, List.get?_eq_none.2,
              Option.getD_none, hblt]
        simp only [h]
      case false =>
        simp only [decide_eq_false_iff_not] at heq
        have R := P (List.length tl)
        rw [List.getD_eq_default] at R
        . rw [List.getD_reverse] at R
          . conv => right; unfold toNatΔ toNatAux
            simp only [List.length_cons, Nat.succ_sub_succ_eq_sub, tsub_zero, ge_iff_le, zero_le, nonpos_iff_eq_zero,
              Nat.sub_self, le_refl, tsub_eq_zero_of_le, List.getElem_eq_get, List.get] at R
            rw [String.toNatAux_accumulates, ← toNatΔ, ← R]
            simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, zero_mul, Nat.sub_self, le_refl, tsub_eq_zero_of_le,
              add_zero]
            apply ih
            . intro i
              rw [P, List.reverse_cons]
              cases h: decide ( i < List.length tl) with
              | true =>
                simp only [decide_eq_true_eq] at h
                rw [List.getD_append]
                simp only [List.length_reverse, h]

              | false =>
                simp only [decide_eq_false_iff_not, not_lt] at h
                rw [List.getD_append_right, ←R, List.getD_singleton_default_eq, List.getD_eq_default] <;> 
                  simp only [List.length_reverse, ge_iff_le, h]
            . apply Nat.le_of_lt_succ
              apply Nat.lt_of_le_of_ne Q heq
          . simp only [List.length_cons, Nat.lt_succ_self]

        . simp only [List.length_cons] at Q
          simp only [List.length_reverse, ge_iff_le]
          apply Nat.le_of_lt_succ
          apply Nat.lt_of_le_of_ne Q heq
          

lemma String.toNatΔ_eq_of_rev_get_eq (P: ∀ i, List.getD a.reverse i '0' = List.getD b.reverse i '0'): String.toNatΔ a = String.toNatΔ b := by
  cases h: decide (List.length a ≤ List.length b) with
  | true =>
    simp only [decide_eq_true_eq] at h
    apply String.toNatΔ_eq_of_rev_get_eq_aux P h
  | false =>
    simp only [decide_eq_false_iff_not, not_le] at h
    apply Eq.symm
    apply (String.toNatΔ_eq_of_rev_get_eq_aux (a:=b) (b:=a) (Q:=le_of_lt h))
    intro i
    apply Eq.symm
    apply P

@[simp]
lemma List.getD_take (P: i < n): List.getD (List.take n l) i d = List.getD l i d := by
  conv => right; rw [← List.take_append_drop n l]
  cases h: decide (i < List.length l) with
  | true =>
    simp only [decide_eq_true_eq] at h
    rw [List.getD_append]
    simp only [length_take, min_le_iff, ge_iff_le, lt_min_iff]
    exact ⟨P,h⟩
  | false =>
    simp only [decide_eq_false_iff_not, not_lt] at h
    rw [List.getD_eq_default, List.getD_eq_default]
    . simp only [take_append_drop, ge_iff_le, h]
    . simp only [length_take, min_le_iff, ge_iff_le, h, or_true]
      
lemma String.toNatΔ_inv_NattoDigits_tail (b n i:ℕ) (Q: b > 1): String.toNatΔ (List.lastN i (Nat.toDigits b n)) = String.toNatΔ (Nat.toDigits b (n % b^i)) := by
  apply String.toNatΔ_eq_of_rev_get_eq
  intro ind
  simp only [ge_iff_le, List.lastN_eq_reverse_take, List.reverse_reverse]
  cases i
  case  zero =>
    simp only [List.take, List.length_nil, zero_le, ge_iff_le, nonpos_iff_eq_zero, List.getD_eq_default,
  Nat.zero_eq, pow_zero, Nat.mod_one, Nat.toDigits_zero, List.reverse_cons, List.reverse_nil, List.nil_append,
  List.length_singleton, List.getD_singleton_default_eq]
  case succ i =>
  cases h: decide (ind < Nat.succ i) with
  | true =>
    simp only [ge_iff_le, decide_eq_true_eq] at h
    simp only [h, List.getD_take]
    rw [Nat.toDigits_modulo] <;> assumption
  | false =>
    simp only [decide_eq_false_iff_not, not_lt] at h
    rw [List.getD_eq_default, List.getD_eq_default]
    . simp only [List.length_reverse, gt_iff_lt, ge_iff_le]
      rw [Nat.toDigits_length_eq_log]
      . calc
        Nat.log b (n % b ^ Nat.succ i) + 1 ≤ Nat.succ i := by
          { 
            apply Nat.succ_le_of_lt
            cases heq: n % b ^ Nat.succ i with
            | zero => simp only [Nat.zero_eq, zero_le, ge_iff_le, nonpos_iff_eq_zero, Nat.log_zero_right, Nat.succ_pos']
            | succ k => 
              rw [← heq]
              apply Nat.log_lt_of_lt_pow
              . simp only [heq, zero_le, ge_iff_le, nonpos_iff_eq_zero, ne_eq, Nat.succ_ne_zero, not_false_iff]
              . apply Nat.mod_lt
                apply Nat.pos_pow_of_pos
                apply Nat.lt_trans Nat.zero_lt_one Q
          }
        _ ≤ ind := h
      . exact Q
    . simp only [List.length_take, List.length_reverse, min_le_iff, ge_iff_le, h, true_or]

    
lemma Nat.toDigits_single_digit (b:ℕ) (n:ℕ) (P: n<b): Nat.toDigits b n = [Nat.digitChar n] := by
  unfold toDigits toDigitsCore
  simp only [_root_.zero_le, ge_iff_le, nonpos_iff_eq_zero, add_eq, add_zero]
  split
  . next => 
    have h:n % b = n := by exact mod_eq_of_lt P
    simp only [h]
  . next =>
    unfold toDigitsCore
    simp only [_root_.zero_le, ge_iff_le, nonpos_iff_eq_zero]
    split
    . simp only [_root_.zero_le, ge_iff_le, nonpos_iff_eq_zero, zero_mod]
    . split
      . next h _=> exfalso; apply h; exact div_eq_of_lt P
      . next h _=> exfalso; apply h; exact div_eq_of_lt P

@[simp]
theorem String.toNatΔ_inv_NattoDigits (n:ℕ) : String.toNatΔ (Nat.toDigits 10 n) = n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      cases n
      case zero => decide
      case succ n=>
        unfold toNatΔ toNatAux
        simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, zero_mul, tsub_le_iff_right, zero_add]
        split
        . next heq => simp only [Nat.toDigits_ne_nil] at heq
        . next s hd tl heq =>
          have h: tl = List.lastN (List.length (Nat.toDigits 10 (Nat.succ n))  - 1) (Nat.toDigits 10 (Nat.succ n)) := by
            simp only [tsub_le_iff_right, ge_iff_le, List.lastN_eq_tail]
            simp only [heq, List.tail_cons]
          apply_fun String.toNatΔ at h
          rw [String.toNatΔ_inv_NattoDigits_tail] at h
          rw [String.toNatAux_accumulates, ← String.toNatΔ]
          rw [h, ih]
          . simp only [gt_iff_lt, Nat.toDigits_length_eq_log, add_tsub_cancel_right, ge_iff_le, add_le_iff_nonpos_left,
              nonpos_iff_eq_zero, Nat.log_eq_zero_iff, or_false, zero_le, tsub_le_iff_right]
            apply Eq.symm
            rw [Nat.add_comm]
            apply Nat.eq_add_of_sub_eq
            . apply Nat.mod_le
            . conv => left; left; rw [← Nat.mod_add_div (Nat.succ n) (10^Nat.log 10 (Nat.succ n))]
              simp only [add_tsub_cancel_left, ge_iff_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero, mul_eq_zero, zero_le,
                Nat.log_pos_iff, and_true, tsub_le_iff_right]
              have h₂: List.getD (Nat.toDigits 10 (Nat.succ n)) 0 '0' = hd := by
                unfold List.getD
                simp only [heq, zero_le, ge_iff_le, nonpos_iff_eq_zero, List.cons.injEq, forall_true_left, and_imp,
                  forall_apply_eq_imp_iff', forall_eq', Option.getD_some,  List.get?]
              rw [Nat.toDigits_eq_digit] at h₂
              have h₃: List.length tl = List.length (Nat.toDigits 10 (Nat.succ n)) -1 := by
                simp only [heq, List.length_cons, Nat.succ_sub_succ_eq_sub, tsub_zero, ge_iff_le, zero_le, nonpos_iff_eq_zero]
              rw [Nat.toDigits_length_eq_log] at h₃
              rw [← h₂, h₃, Nat.digitChar_sub_zero_eq_self, Nat.toDigits_length_eq_log, Nat.digit, Nat.mul_comm]
              simp only [add_tsub_cancel_right, ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, Nat.log_eq_zero_iff,
                or_false, zero_le, tsub_zero, mul_eq_mul_right_iff, Nat.log_pos_iff, and_true]
              left
              apply Eq.symm (Nat.mod_eq_of_lt _)
              . apply (Nat.div_lt_iff_lt_mul _).2
                . rw [← pow_succ]
                  apply Nat.lt_pow_of_log_lt
                  . simp only
                  . simp only [lt_add_iff_pos_right]
                . simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, gt_iff_lt, pow_pos]
              . simp only
              . simp only [tsub_le_iff_right, ge_iff_le, zero_le, nonpos_iff_eq_zero, tsub_zero, tsub_eq_zero_iff_le,
                gt_iff_lt, Nat.digit_lt_base]
              . simp only
              . simp only
              . apply Nat.pos_of_ne_zero
                intro hp
                apply Nat.toDigits_ne_nil (List.length_eq_zero.1 hp)
              
          . simp only [gt_iff_lt, Nat.toDigits_length_eq_log, add_tsub_cancel_right, ge_iff_le, add_le_iff_nonpos_left,
              nonpos_iff_eq_zero, Nat.log_eq_zero_iff, or_false, zero_le]
            
            calc
              (Nat.succ n) % 10 ^ Nat.log 10 (Nat.succ n) < 10 ^ Nat.log 10 (Nat.succ n) :=  by apply Nat.mod_lt; apply Nat.pos_pow_of_pos; simp only
              _ ≤  n + 1  := by apply Nat.pow_log_le_self; simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, ne_eq, Nat.succ_ne_zero, not_false_iff]
            
          . simp only

@[simp]
theorem String.toIntΔ_inv_IntreprΔ (i:ℤ): String.toIntΔ (Int.reprΔ i) = i := by
  unfold toIntΔ Int.reprΔ
  cases i with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe]
    split
    case h_1 s heq =>
      simp only [Nat.toDigits_ne_nil
    ] at heq
    case h_2 head tail heq =>
      split
      case inl h =>
        have h₂: (List.all (head::tail) Char.isDigit == true) = true := by
          rw [← heq]
          apply Nat.toDigits_digits <;> decide
        simp at h₂
        have ⟨ h₃, _⟩ :=h₂
        simp only [h] at h₃
      . simp only [← heq, toNatΔ_inv_NattoDigits]
  | negSucc n =>
    simp only [List.singleton_append, toNatΔ_inv_NattoDigits, Nat.cast_succ, neg_add_rev, ite_true,
      Int.negSucc_eq]

lemma List.eq_append_of_getRest [DecidableEq α] {l l₁ l₂: List α} (P: List.getRest l l₁ = some l₂): l = l₁ ++ l₂ := by
  induction l₁ generalizing l l₂ with
  | nil =>
    unfold getRest at P
    simp only [Option.some.injEq] at P
    simp only [P, nil_append]
  | cons head tail ih =>
    unfold getRest at P
    split at P
    case h_1 heq => simp only at heq
    case h_2 => simp only at P
    case h_3 hd tl y l₁ heq =>
      split at P
      case inr heq₂ => contradiction
      case inl heq₂ =>
        injection heq
        subst hd y l₁
        simp only [cons_append, cons.injEq, true_and]
        apply ih
        apply P


@[simp]
lemma List.getRest_nil [DecidableEq α] {l: List α}: List.getRest l [] = l := by
  unfold getRest
  simp only

@[simp]
lemma List.getRest_delim_append [DecidableEq α] {l₁ l₂: List α}: List.getRest (l₁ ++ l₂) l₁ = some l₂ := by
  induction l₁ with
  | nil => simp only [nil_append, getRest_nil]
  | cons head tail ih =>
    unfold getRest
    simp only [cons_append, ih, ite_true]

@[simp]
lemma List.nil_isInfix: [] <:+: l := by
  unfold List.isInfix
  exists []
  exists l
  
@[simp]
lemma List.nil_isPrefix: [] <+: l := by
  unfold List.isPrefix
  exists l


@[simp]
lemma List.nil_isSuffix: [] <:+ l := by
  unfold List.isSuffix
  simp only [append_nil, exists_eq]

lemma List.isInfix_cons {head:α} {l tail: List α} (h: l <:+: tail):  l <:+: head::tail := by
  unfold List.isInfix at *
  match h with
  | ⟨s,  t, P⟩ =>
    exists head::s,  t
    simp only [cons_append, append_assoc, ← P]

@[simp]
lemma List.isInfix_append_left (l₁ l₂:List α): l₁ <:+: (l₁ ++ l₂) := by exact ⟨ [], l₂, rfl⟩

@[simp]
lemma List.isInfix_append_right (l₁ l₂:List α): l₂ <:+: (l₁ ++ l₂) := by exact ⟨ l₁, [], List.append_nil _⟩

@[simp]
lemma List.isInfix_self: l <:+: l := by exact ⟨[], [], List.append_nil _⟩

    
@[simp]
lemma List.getRest_none [DecidableEq α] {l₁ l₂:List α}: List.getRest l₁ l₂ = none ↔ ¬ l₂ <+: l₁ := by
  apply iff_not_comm.1
  rw [← ne_eq, Option.ne_none_iff_exists]
  apply Iff.intro
  . intro ⟨l₃, h⟩
    subst h
    exists l₃
    exact Eq.symm getRest_delim_append
  . intro ⟨l₃, h⟩
    exists l₃
    exact Eq.symm (eq_append_of_getRest (Eq.symm h))


theorem List.sizeOf_getRest [DecidableEq α] {l l₁ l₂: List α} (h: List.getRest l l₁ = some l₂) : sizeOf l₂ = 1 + sizeOf l - sizeOf l₁ := by
  induction l generalizing l₁ l₂ with
  | nil => 
    unfold getRest at h
    cases l₁
    . simp only [Option.some.injEq] at h
      subst h
      simp only [nil.sizeOf_spec, add_tsub_cancel_right, ge_iff_le]
    . simp only at h
  | cons head tail ih =>
    unfold getRest at h
    split at h <;> try contradiction
    case h_1 heq => injection h; simp_all only [tsub_le_iff_right, ge_iff_le, nil.sizeOf_spec, add_tsub_cancel_left, add_le_iff_nonpos_right,
       nonpos_iff_eq_zero, zero_le]
    case h_3 heq =>
      split at h <;> try contradiction
      case inl heq₂ =>
        injection heq
        subst_vars
        simp only [ih h, tsub_le_iff_right, ge_iff_le, cons.sizeOf_spec, sizeOf_default, add_zero, zero_le,
          nonpos_iff_eq_zero, Nat.add_sub_add_left, add_le_add_iff_left]

theorem List.sizeOf_pos (l:List α): sizeOf l > 0 := by
  cases l <;> simp only [cons.sizeOf_spec, nil.sizeOf_spec, sizeOf_default, add_zero, zero_le, ge_iff_le, nonpos_iff_eq_zero, gt_iff_lt,
    add_pos_iff, true_or]

def List.splitOnListAux [DecidableEq α] (delim: List α) (l:List α) (acc: Array α) (r: Array (Array α)) (delim_nonempty: delim ≠ []): (Array (Array α)) :=
  match _h₀: l with
  | [] => r.push acc
  | head::tail =>
    match h: getRest l delim with
    | none => 
      List.splitOnListAux delim tail (acc.push head) r delim_nonempty
    | some rest => 
      have _: sizeOf rest < sizeOf l := by
        rw [List.sizeOf_getRest h]
        cases delim with
        | nil => contradiction
        | cons hd tail =>
          simp only [cons.sizeOf_spec, sizeOf_default, add_zero, zero_le, ge_iff_le, nonpos_iff_eq_zero,
            Nat.add_sub_add_left, tsub_le_iff_right, add_le_add_iff_left]
          apply Nat.sub_lt (List.sizeOf_pos l) (List.sizeOf_pos tail)

      List.splitOnListAux delim rest #[] (r.push acc) delim_nonempty
decreasing_by try simp_wf; try decreasing_tactic

def List.splitOnList [DecidableEq α] (delim: List α) (l: List α): List (List α) :=
  match delim with
  | [] => [l]
  | head::tail  => 
    Array.toList (Array.map Array.toList (splitOnListAux (head::tail) l #[] #[] (by simp only [ne_eq])))



def Array.modifyHead (F: α→ α) (a:Array α): Array α :=
  Array.modify a 0 F


theorem Array.data_injective : Function.Injective (Array.data (α:=α)) := by
  unfold Function.Injective
  intro a₁ a₂ h
  rw [← Array.toArray_data a₁, ← Array.toArray_data a₂]
  congr

@[elab_as_elim]
lemma List.induction_by_length_on {p : List α → Prop} (l : List α)
    (h : ∀ l, (∀ l₂, List.length l₂ < List.length l → p l₂) → p l) : p l :=
  h l fun l₂ _ => List.induction_by_length_on l₂ h
termination_by _ => l.length


@[simp]
theorem List.splitOnListAux_r [DecidableEq α] {delim l: List α} (h):
  List.splitOnListAux delim l acc (r++rest) h = r ++ List.splitOnListAux delim l acc rest h := by
  induction l using List.induction_by_length_on generalizing acc r rest with
  | h l ih =>
    unfold splitOnListAux
    split
    case h_1 =>
      simp only [Array.ext_iff, Array.push_data, Array.append_data, append_assoc]
    case h_2 head tail =>
      split
      case h_1 heq₂ =>
        simp only [length_cons, gt_iff_lt, Nat.lt_succ_self, ih]
      case h_2 rst heq₂ =>
        simp only
        have h₃: Array.push (r ++ rest) acc = r ++ (Array.push rest acc) := by
          simp only [Array.ext_iff, Array.push_data, Array.append_data, append_assoc]
        rw [h₃, ih]
        have h₄:= List.eq_append_of_getRest heq₂
        simp only [h₄, length_append, lt_add_iff_pos_left, zero_le, ge_iff_le, nonpos_iff_eq_zero,
          Nat.pos_iff_ne_zero, ne_eq, length_eq_zero, h, not_false_iff]

@[simp]
lemma Array.modifyHead_data (a:Array α): (Array.modifyHead f a).data = List.modifyHead f a.data := by
  unfold modifyHead modify modifyM Id.run
  split
  case inl heq =>
    simp [List.set_eq_take_cons_drop _ heq]
    split
    case h_1 heq₂ =>
      apply_fun (@List.toArray α) at heq₂
      simp only [toArray_data] at heq₂
      subst heq₂
      simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, size_toArray, List.length_nil, lt_self_iff_false] at heq
    case h_2 head tail heq₂ =>
      apply_fun (@List.toArray α) at heq₂
      simp only [toArray_data] at heq₂
      subst heq₂
      simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, data_toArray, List.tail_cons, List.cons.injEq, and_true]
      congr
      simp [Array.getElem_eq_data_get, Array.data_toArray (head::tail)] 
      simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, List.get_eq_iff, data_toArray, List.cons.injEq,
        forall_true_left, and_imp, forall_apply_eq_imp_iff', forall_eq', List.get?_zero, List.head?_cons]
  case inr heq =>
    simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, not_lt] at heq
    rw [← Array.toArray_data a, Array.size_toArray, List.length_eq_zero] at heq
    simp only [Id.pure_eq, heq, List.modifyHead]


theorem List.splitOnListAux_acc [DecidableEq α] {delim l: List α} (acc: Array α) {h}:
  List.splitOnListAux delim l acc #[] h =
   Array.modifyHead (Array.append acc) (List.splitOnListAux delim l #[] #[] h) := by
  induction l using List.induction_by_length_on generalizing acc with
  | h l ih =>
    unfold splitOnListAux
    split
    case h_1 heq =>
      simp [Array.ext_iff]
    case h_2 head tail =>
      split
      case h_1 heq =>
        rw [ih (acc:= Array.push acc head), ih (acc:= Array.push #[] head)]
        . simp only [Array.ext_iff, Array.modifyHead_data, modifyHead, Array.append_eq_append]
          cases (splitOnListAux delim tail #[] #[] h).data with
          | nil => simp only
          | cons => 
            simp only [cons.injEq, Array.ext_iff, Array.append_data, Array.push_data, append_assoc, singleton_append,
              Array.data_toArray, nil_append, and_self]
        . simp only [length_cons, Nat.lt_succ_self]
        . simp only [length_cons, Nat.lt_succ_self]
      case h_2 heq =>
        have h₁: (Array.push #[] acc) = (Array.push #[] acc) ++ #[] := by simp [Array.ext_iff]
        have h₂: (Array.push #[] #[]) = (Array.push #[] (#[]:Array α)) ++ #[] := by simp [Array.ext_iff]
        rw [h₁,h₂,List.splitOnListAux_r, List.splitOnListAux_r]
        simp [Array.ext_iff]

@[simp]
theorem List.splitOnListAux_delim [DecidableEq α]  {delim l: List α} (h): 
    List.splitOnListAux delim (delim ++ l) acc r h = r ++ #[acc] ++ List.splitOnListAux delim l #[] #[] h := by
  conv => left; unfold splitOnListAux
  have ⟨head, tail, heq⟩ :=List.exists_cons_of_ne_nil h
  subst heq
  simp only [cons_append]
  split
  case h_1 heq =>
    unfold getRest at heq
    simp at heq
  case h_2 rest heq =>
    have h₂ : (Array.push r acc) = r ++ #[acc] ++ #[] := by simp only [Array.ext_iff, Array.push_data, Array.append_data, Array.data_toArray, append_nil]
    rw [h₂, List.splitOnListAux_r]
    congr
    have h₃ := List.eq_append_of_getRest heq
    simp_all only [ne_eq, not_false_iff, cons_append, cons.injEq, append_cancel_left_eq, true_and]


theorem List.splitOnListAux_nonmatching [DecidableEq α] (l:List α) (h₁: ¬delim <:+: l) {h}: List.splitOnListAux delim l #[] #[]  h = #[l.toArray] := by
  unfold splitOnListAux
  split
  case h_1 =>
    simp only [Array.ext_iff, Array.push_data, Array.data_toArray, nil_append]
  case h_2 head tail =>
    split
    case h_1 heq =>
      rw [List.splitOnListAux_acc, List.splitOnListAux_nonmatching tail]
      . simp only [Array.ext_iff, Array.modifyHead_data, modifyHead, Array.data_toArray, Array.append_eq_append,
          cons.injEq, Array.append_data, Array.push_data, nil_append, singleton_append, and_self]
      . intro contr
        apply h₁
        exact List.isInfix_cons contr
    case h_2 head tail heq =>
      simp only [List.eq_append_of_getRest heq, isInfix_append_left, not_true] at h₁

@[simp]
theorem List.splitOnList_nonmatching [DecidableEq α] (l:List α) (h₁: ¬delim <:+: l): List.splitOnList delim l = [l] := by
  unfold List.splitOnList
  cases delim with
  | nil => simp only
  | cons => 
    simp only
    rw [List.splitOnListAux_nonmatching]
    . simp only [Array.toList_eq, Array.map_data, map, Array.data_toArray]
    . exact h₁

lemma List.isInfix_of_isPrefix (h: l₁ <+: l₂): l₁<:+: l₂ := ⟨[],h⟩

@[simp]
lemma List.isPrefix_self: l <+: l := ⟨[], List.append_nil l⟩ 

@[simp]
lemma List.take_isPrefix: List.take n l <+: l := ⟨ List.drop n l, take_append_drop n l⟩ 

@[simp]
lemma List.isPrefix_take {delim l: List α}:  delim <+: take (List.length delim) l ↔ delim <+: l := by
  apply Iff.intro
  . intro ⟨t, heq⟩
    replace heq := congr_arg (take (length delim)) heq
    simp only [take_left, take_take, min_self] at heq
    rw [heq]
    simp only [take_isPrefix]
  . intro ⟨t, heq⟩
    subst l
    simp only [take_left, isPrefix_self]


@[simp]
lemma List.dropLast_take': List.dropLast (List.take n l) = List.take ((min n (length l)) - 1) l := by
  cases h: decide (n < length l) with
  | true => 
    simp only [decide_eq_true_eq] at h
    simp only [List.dropLast_take h, Nat.pred_eq_sub_one, tsub_le_iff_right, ge_iff_le, min_eq_left (le_of_lt h)]
  | false =>
    simp only [decide_eq_false_iff_not, not_lt] at h
    rw [List.take_length_le h]
    simp only [dropLast_eq_take, Nat.pred_eq_sub_one, tsub_le_iff_right, ge_iff_le, min_le_iff, h, min_eq_right]

@[simp]
lemma List.isPrefix_of_append_isPrefix_append (h: l₁ ++ l₂ <+: l₁ ++ l₃): l₂ <+: l₃ := by
  have ⟨t, heq⟩ := h
  simp only [append_assoc, append_cancel_left_eq] at heq
  exact ⟨t, heq⟩


lemma List.splitOnListAux_progress [DecidableEq α] {delim front rest: List α} (h₁: ¬ delim <:+: (front ++  delim.dropLast)) {h₂:_}:  
    List.splitOnListAux delim (front ++ delim ++ rest) #[] #[] h₂ = #[List.toArray front] ++  List.splitOnListAux delim rest #[] #[] h₂ := by
  induction front with
  | nil =>
    rw [nil_append, splitOnListAux_delim]
    simp only [Array.ext_iff, Array.append_data, Array.data_toArray, nil_append, singleton_append]
  | cons head tail ih =>
    conv => left; unfold splitOnListAux
    split
    case h_1 heq =>
      simp only [cons_append, append_assoc] at heq
    case h_2 head tail heq =>
      split
      case h_1 heq₂ =>
        injection heq; subst_vars
        conv => left; rw [List.splitOnListAux_acc]
        simp only [List.append_eq, append_assoc]
        simp only [append_assoc] at ih
        rw [ih]
        . simp only [Array.ext_iff, Array.modifyHead_data, modifyHead, Array.append_data, Array.data_toArray,
            singleton_append, Array.append_eq_append, cons.injEq, Array.push_data, nil_append, and_self]
        . intro h
          apply h₁
          simp only [cons_append, h, isInfix_cons]
      case h_2 hd tl rest₂ heq₂ =>
        exfalso; apply h₁
        apply List.isInfix_of_isPrefix
        have h₃ := congr_arg (List.take (List.length delim)) (List.eq_append_of_getRest heq₂)
        rw [List.take_append_of_le_length] at h₃
        simp at h₃
        conv => left; rw [← h₃]
        simp only [length_take, length_cons, length_append, min_le_iff, ge_iff_le, cons_append]
        apply List.isPrefix_take.1
        simp only [length_take, length_cons, length_append, min_le_iff, ge_iff_le]
        rw [min_eq_left]
        . have h₄: take (length delim) (hd :: (tl ++ delim)) = take (length delim) (hd :: (tl ++ delim.dropLast)) := by
            rw [← List.cons_append, ← List.cons_append,
            List.take_append_eq_append_take, List.take_append_eq_append_take]
            rw [List.dropLast_eq_take, List.take_take, min_eq_left]
            simp only [length_cons, tsub_le_iff_right, ge_iff_le]
            calc
              length delim ≤  Nat.pred (length delim) + 1 := by simp only [Nat.pred_eq_sub_one, tsub_le_iff_right, ge_iff_le, le_refl, Nat.le_add_of_sub_le]
              _ ≤  Nat.pred (length delim) + Nat.succ (length tl) := by simp only [Nat.succ_eq_add_one, add_le_add_iff_left, le_add_iff_nonneg_left, zero_le, ge_iff_le,
                nonpos_iff_eq_zero]
          rw [h₄]
          simp only [isPrefix_self]
        . simp only [Nat.succ_eq_add_one, Nat.le_add_one_iff, le_add_iff_nonneg_left, zero_le, ge_iff_le,
            nonpos_iff_eq_zero, true_or]
        . simp only [cons_append, length_cons, length_append, le_add_iff_nonneg_left, zero_le, ge_iff_le,
            nonpos_iff_eq_zero, Nat.le_succ_of_le]

theorem List.splitOnList_progress [DecidableEq α] {delim front rest: List α} (h₁: ¬ delim <:+: (front ++  delim.dropLast)):  
    List.splitOnList delim (front ++ delim ++ rest) = [front] ++  List.splitOnList delim rest := by
  unfold splitOnList
  cases delim with
  | nil =>
    simp only [dropLast, append_nil, nil_isInfix, not_true] at h₁
  | cons head tail=>
    simp only
    rw [List.splitOnListAux_progress]
    simp only [Array.toList_eq, Array.map_data, Array.append_data, Array.data_toArray, singleton_append]
    simp only [map, Array.toList_eq, Array.data_toArray]
    exact h₁

@[simp]
lemma List.join_intersperse_nil (l:List (List α)): join (intersperse [] l) = join l := by
  match l with
  | [] => simp only [join]
  | [a] => simp only [join, append_nil]
  | a :: b :: tail =>
    simp only [join, List.join_intersperse_nil, nil_append]
  
def Array.modifyLast (f: α → α) (a:Array α): Array α := Array.modify a (size a-1) f

@[simp]
lemma Array.modify_data (a:Array α) (i:ℕ) (f:α → α): Array.data (Array.modify a i f) = List.modifyNth f i a.data := by
  unfold modify Id.run modifyM
  split
  . simp
    rw [List.modifyNth_eq_set_get]
    congr 1
  case inr heq =>
    simp at heq
    rw [List.modifyNth_eq_set_get?]
    simp [List.get?_eq_none.2 heq]

@[simp]
lemma List.modifyLast_nil: List.modifyLast f [] = [] := by
  unfold modifyLast modifyLast.go
  simp only

@[simp]
lemma List.modifyNth_nil: List.modifyNth f i [] = [] := by
  simp [List.modifyNth_eq_set]

lemma List.modifyLast_cons {head: α} {tail: List α} (h: tail ≠ []): modifyLast f (head::tail) = head :: modifyLast f tail := by
  rw [← List.dropLast_append_getLast (List.cons_ne_nil head tail),← List.dropLast_append_getLast h,
   List.modifyLast_append_one, List.modifyLast_append_one]
  simp only [append_eq_nil, and_false, IsEmpty.forall_iff, dropLast_concat, ne_eq, not_false_iff, getLast_cons,
    getLast_append, cons_append, dropLast]

lemma List.modifyLast_eq_modifyNth: List.modifyLast f l = List.modifyNth f (length l - 1) l :=  by
  cases l with
  | nil => simp only [modifyLast_nil, length_nil, zero_le, ge_iff_le, nonpos_iff_eq_zero, Nat.zero_sub, tsub_eq_zero_of_le, modifyNth_nil]
  | cons head tail =>
    rw [← List.dropLast_append_getLast (List.cons_ne_nil head tail)]
    simp [List.modifyLast_append_one,List.modifyNth_eq_take_drop, List.take_append_eq_append_take]
    rw [List.take_all_of_le, List.drop_append_eq_append_drop]
    simp only [ne_eq, length_dropLast, length_cons, Nat.succ_sub_succ_eq_sub, tsub_zero, ge_iff_le, zero_le,
      nonpos_iff_eq_zero, Nat.sub_self, le_refl, tsub_eq_zero_of_le,
      append_cancel_left_eq, drop]
    split
    case h_1 heq => simp only [ne_eq, append_eq_nil, and_false] at heq
    case h_2 heq => 
      rw [List.drop_eq_nil_of_le] at heq
      simp_all only [tsub_le_iff_right, ge_iff_le, ne_eq, nil_append, cons.injEq]
      simp only [length_dropLast, length_cons, Nat.succ_sub_succ_eq_sub, tsub_zero, ge_iff_le, zero_le,
        nonpos_iff_eq_zero, le_refl]
    simp only [length_dropLast, length_cons, Nat.succ_sub_succ_eq_sub, tsub_zero, ge_iff_le, zero_le,
      nonpos_iff_eq_zero, le_refl]

@[simp]
lemma Array.modifyLast_data: (Array.modifyLast f a).data = List.modifyLast f a.data := by
  unfold modifyLast
  rw [List.modifyLast_eq_modifyNth]
  simp only [tsub_le_iff_right, ge_iff_le, modify_data]


lemma Nat.sub_sub_eq_add_sub_of_le  {a b c:ℕ} (h:c≤ b): a - (b-c) = a + c - b := by
  induction a generalizing b c with
  | zero => simp only [Nat.zero_eq, zero_le, ge_iff_le, nonpos_iff_eq_zero, tsub_le_iff_right, Nat.zero_sub,
    tsub_eq_zero_of_le, zero_add, h]
  | succ a ih =>
    cases hle: decide (a ≥ (b-c)) with
    | true => 
      simp only [ decide_eq_true_eq] at hle
      rw [Nat.succ_sub hle]
      simp only [tsub_le_iff_right, ge_iff_le] at hle
      rw [Nat.succ_add, Nat.succ_sub hle, ih h]

    | false =>
      simp only [ decide_eq_false_iff_not, not_le] at hle
      have hle₂ := Nat.succ_le_of_lt hle
      rw [Nat.sub_eq_zero_of_le hle₂]
      have hle₃ := Nat.add_le_of_le_sub h hle₂
      rw [Nat.sub_eq_zero_of_le hle₃]

    
def List.isInfixOf [BEq α] : List α → List α → Bool
  | [], [] => true
  | _, [] => false
  | delim, a::as => isPrefixOf delim (a::as) || isInfixOf delim as

lemma List.isPrefixOf_ext [BEq α] [LawfulBEq α] (delim l:List α): isPrefixOf delim l = true ↔ isPrefix delim l := by
  apply Iff.intro
  . intro h
    induction l  generalizing delim
    case nil =>
      unfold isPrefixOf at h
      cases delim <;> simp_all only [isPrefix_self]
    case cons head tail ih =>
      unfold isPrefixOf at h
      cases delim
      case nil => simp only [append_nil, nil_isPrefix]
      case cons dhead dtail =>
        simp at h
        have ⟨h₂,h₃⟩ := h
        have ⟨s, heq⟩  := ih dtail h₃
        exists s
        simp only [h₂, cons_append, heq]
  . intro h
    have ⟨s, heq⟩ := h
    rw [← heq]
    clear heq h
    induction delim generalizing l
    case nil =>
      unfold isPrefixOf
      simp only
    case cons head tail ih =>
      unfold isPrefixOf
      simp
      apply ih l


lemma List.isInfixOf_ext [BEq α] [LawfulBEq α](delim l:List α): isInfixOf delim l = true ↔ isInfix delim l := by
  apply Iff.intro
  . intro h
    induction l
    case nil => 
      unfold isInfixOf at h
      split at h
      . simp only [nil_isInfix]
      . simp only at h
      . next heq => simp only at heq
    case cons head tail ih =>
      unfold isInfixOf at h
      simp at h
      cases h with
      | inl heq =>
        simp only [List.isPrefixOf_ext] at heq
        simp only [heq, List.isInfix_of_isPrefix]
      | inr heq =>
        have h₂:= ih heq
        apply List.isInfix_cons h₂
  . intro h
    have ⟨s,t, heq⟩ := h
    subst heq
    clear h
    induction s
    case nil =>
      unfold isInfixOf
      split
      case h_1 => simp only
      case h_2 hne heq => simp_all only [nil_append, append_eq_nil, forall_true_left]
      case h_3 heq => 
        simp at heq
        rw [← heq]
        simp only [Bool.or_eq_true, List.isPrefixOf_ext]
        left
        exists t
    case cons head tail ih =>
      unfold isInfixOf
      split
      case h_1 heq=>
        simp only [append_assoc, cons_append, append_eq_nil, and_false] at heq
      case h_2 hne heq =>
        simp only [append_assoc, cons_append, append_eq_nil, and_false] at heq
      case h_3 hd tl heq =>
        simp at heq
        have ⟨h₁, h₂⟩ := heq
        simp only [Bool.or_eq_true]
        right
        rw [ ← h₂]
        rw [append_assoc] at ih
        apply ih

@[simp]
lemma List.isPrefix_self_append: l₁ <+: l₁ ++ l₂ := by exists l₂

lemma List.isPostfix_append_of_isPostfix (h:l₁ <:+ l₂): l₁ <:+ l₃ ++ l₂ := by
  have ⟨s, heq⟩ := h
  rw [← heq]
  exists l₃ ++ s
  rw [append_assoc]

lemma List.isInfix_append_left_of_isInfix (h:l₁ <:+: l₂): l₁ <:+: l₃ ++ l₂ := by
  have ⟨s, t, heq⟩ := h
  rw [← heq]
  exists l₃ ++ s, t
  simp only [append_assoc]

lemma List.isInfix_append_right_of_isInfix (h:l₁ <:+: l₂): l₁ <:+: l₂ ++ l₃ := by
  have ⟨s, t, heq⟩ := h
  rw [← heq]
  exists s, t ++ l₃
  simp only [append_assoc]

lemma List.isPrefix_append (h: l₁ <+: l₂ ++ l₃): take (length l₂) l₁ <+: l₂ ∧ drop (length l₂) l₁ <+: l₃ := by
  have ⟨t, heq⟩ := h
  apply And.intro
  . apply_fun take (length l₂) at heq
    simp only [take_append_eq_append_take, tsub_le_iff_right, ge_iff_le, take_length, Nat.sub_self, zero_le,
      nonpos_iff_eq_zero, le_refl, tsub_eq_zero_of_le, append_nil, take] at heq
    conv => right; rw [← heq]
    apply isPrefix_self_append
  . apply_fun drop (length l₂) at heq
    simp only [drop_append_eq_append_drop, tsub_le_iff_right, ge_iff_le, drop_length, Nat.sub_self, zero_le,
      nonpos_iff_eq_zero, le_refl, tsub_eq_zero_of_le, nil_append, drop] at heq
    conv => right; rw [← heq]
    apply isPrefix_self_append

lemma List.append_isPrefix_split (h:s ++ l₁ <+: l₂) n: s ++ l₁ <+: (take n l₂) ∨ drop (n + 1 - length l₁) s ++ l₁ <+: (drop (n + 1 - length l₁) l₂) := by
  have ⟨t,heq⟩ := h
  rw [← heq]
  cases hle: decide (length s + length l₁ ≤ n) with
  | true =>
    simp only [decide_eq_true_eq] at hle
    left
    exists (take (n-length s - length l₁) t)
    have hle₁ : length s ≤ n := by  calc
      length s ≤  length s + length l₁ := by simp
             _ ≤  n                     := hle
    have hle₂ : length l₁ ≤ (n - length s) := by apply Nat.le_sub_of_add_le; rw [add_comm]; exact hle
    rw [List.take_append_eq_append_take, List.take_append_eq_append_take, List.take_all_of_le hle₁, List.take_all_of_le hle₂]
    simp
    congr 1
    apply Nat.sub_sub
  | false =>
    simp only [decide_eq_false_iff_not, not_le] at hle
    right
    rw [List.drop_append_eq_append_drop, List.drop_append_eq_append_drop]
    have heq₁: n + 1 - length l₁ - length s = 0 := by
      rw [Nat.sub_sub, Nat.sub_eq_zero_of_le]
      apply Nat.add_one_le_iff.2
      rw [Nat.add_comm]
      apply hle
    rw [heq₁, drop]
    exists (drop (n + 1 - length l₁ - length (s ++ l₁)) t)

lemma List.isInfix_split (h: l₁ <:+: l₂) n: l₁ <:+: (take n l₂) ∨  l₁ <:+: (drop (n + 1 - length l₁) l₂) := by
  have ⟨s, hPre⟩ := h
  cases append_isPrefix_split hPre n with
  | inl => left; exists s
  | inr => right; exists (drop (n + 1 - length l₁) s)

lemma List.isInfix_append_split_left (h: l₁ <:+: l₂ ++ l₃): l₁ <:+: l₂ ∨ l₁ <:+: l₂.lastN (l₁.length -1) ++ l₃ := by
  have split := List.isInfix_split h l₂.length
  simp only [take_left, ge_iff_le]  at split
  cases split with
  | inl h₁ =>
    left; assumption
  | inr h₂ =>
    right
    if hzero: l₁.length = 0 then
      simp [List.length_eq_zero.1 hzero]
    else
      rw [List.drop_append_of_le_length] at h₂
      . rw [lastN]
        convert h₂ using 3
        rw [Nat.sub_sub_eq_add_sub_of_le]
        rw [Nat.succ_le, pos_iff_ne_zero]
        apply hzero
      . simp only [ge_iff_le, tsub_le_iff_right, add_le_add_iff_left]
        rw [Nat.succ_le, pos_iff_ne_zero]
        apply hzero

lemma List.isInfix_append_split_right (h: l₁ <:+: l₂ ++ l₃): l₁ <:+: l₂ ++ l₃.take (l₁.length - 1) ∨ l₁ <:+: l₃ := by
  have split := List.isInfix_split h (l₂.length + (l₁.length -1))
  if hzero: l₁.length = 0 then
      simp only [List.length_eq_zero.1 hzero, length_nil, ge_iff_le, tsub_eq_zero_of_le, append_nil, nil_isInfix, or_self]
  else
    cases split with
    | inl h₁ =>
      left
      rw [List.take_append] at h₁
      exact h₁
    | inr h₂ =>
      right
      rw [add_assoc, Nat.sub_add_cancel, Nat.add_sub_cancel, ←Nat.add_zero l₂.length, List.drop_append, List.drop] at h₂
      . exact h₂
      . rw [Nat.succ_le_iff, Nat.pos_iff_ne_zero]
        exact hzero

  

lemma List.isInfix_of_isInfix_take (h: l₁ <:+: take n l₂): l₁ <:+: l₂ := by
  rw [← List.take_append_drop n l₂]
  have ⟨s,t,heq⟩ := h
  exists s, t ++ drop n l₂
  simp only [append_assoc, ← heq]

lemma List.isInfix_of_isInfix_drop (h: l₁ <:+: drop n l₂): l₁ <:+: l₂ := by
  rw [← List.take_append_drop n l₂]
  have ⟨s,t,heq⟩ := h
  exists take n l₂ ++ s, t
  simp only [append_assoc, ← heq]

lemma List.isInfix_of_isInfix_lastN (h: l₁ <:+: lastN n l₂): l₁ <:+: l₂ := by
  rw [lastN] at h
  apply List.isInfix_of_isInfix_drop h

lemma List.isPrefix_trans (h₁: l₁ <+: l₂) (h₂: l₂ <+: l₃): l₁ <+: l₃:= by
  have ⟨t₁, heq₁⟩ := h₁
  have ⟨t₂, heq₂⟩ := h₂
  rw [← heq₂, ←heq₁, append_assoc]
  exists (t₁ ++ t₂)
  
lemma List.isInfix_trans (h₁: l₁ <:+: l₂) (h₂: l₂ <:+: l₃): l₁ <:+: l₃:= by
  have ⟨s₁, t₁, heq₁⟩ := h₁
  have ⟨s₂, t₂, heq₂⟩ := h₂
  rw [← heq₂, ←heq₁, append_assoc]
  exists (s₂ ++ s₁), (t₁ ++ t₂)
  simp only [append_assoc]

lemma List.isInfix_first_match [DecidableEq α] (l₁ l₂: List α) (h: l₁ <:+: l₂) (hne: l₁ ≠ []): ∃ s, s ++ l₁ <+: l₂ ∧ ¬ l₁ <:+: s ++ l₁.dropLast := by
  have ⟨s, t, heq⟩ := h
  cases hinf: List.isInfixOf l₁ (s ++ dropLast l₁) with
  | true => 
    simp [List.isInfixOf_ext] at hinf
    have _ : length s + (length l₁ - 1) < length l₂ := by 
      rw[← heq]
      simp only [length_append, length_dropLast, tsub_le_iff_right, ge_iff_le, append_assoc, add_lt_add_iff_left]
      apply Nat.lt_add_right
      apply Nat.sub_lt
      . apply Nat.pos_of_ne_zero
        simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, ne_eq, length_eq_zero, hne, not_false_iff]
      . simp only
    
    have  ⟨s₁, ih⟩  := List.isInfix_first_match _ _ hinf hne
    exists s₁
    apply And.intro
    . rw [← heq]
      apply isPrefix_trans ih.left
      exists (l₁.lastN 1) ++ t
      rw [dropLast_eq_take, lastN, Nat.pred_eq_sub_one]
      simp only [tsub_le_iff_right, ge_iff_le, append_assoc, append_cancel_left_eq]
      rw [← append_assoc, List.take_append_drop (length l₁ - 1) l₁]
      
    . exact ih.right
  | false =>
    exists s
    apply And.intro
    . exists t
    . simp only [←isInfixOf_ext, hinf, not_false_iff]
termination_by isInfix_first_match _ l _ _=> (length l)


lemma List.splitOnListAux_ne_nil [DecidableEq α] (l:List α): List.splitOnListAux delim l acc r h ≠ #[] := by
  unfold splitOnListAux
  cases l with
  | nil => simp only; intro contr; rw [Array.ext_iff] at contr; simp only [Array.push_data, Array.data_toArray, append_eq_nil, and_false] at contr
  | cons head tail =>
    simp only
    match h: getRest (head::tail) delim with
    | none => 
      simp only
      have _ : length tail < Nat.succ (length tail) := by apply Nat.lt_succ_self
      apply List.splitOnListAux_ne_nil tail
    | some rest => 
      simp only
      have _ : length rest < Nat.succ (length tail) := by
        have h₂ := List.eq_append_of_getRest h
        replace h₂ := congr_arg List.length h₂
        simp at h₂
        rw[h₂]
        apply Nat.lt_add_of_pos_left
        apply Nat.zero_lt_of_ne_zero
        intro contr
        have contr₂ := List.length_eq_zero.1 contr
        contradiction
      apply List.splitOnListAux_ne_nil rest
termination_by splitOnListAux_ne_nil l => length l
decreasing_by try simp_wf; try decreasing_tactic

lemma List.drop_isInfix: List.drop n l <:+: l := by
  exists List.take n l, []
  simp only [take_append_drop, append_nil]

lemma List.drop_isInfix_drop (h: n ≥ m): List.drop n l <:+: List.drop m l := by
  rw [← Nat.add_sub_of_le h, add_comm, List.drop_add]
  apply List.drop_isInfix

lemma List.take_isInfix: List.take n l <:+: l := by
  exists [], drop n l
  simp only [nil_append, take_append_drop]

lemma List.take_isInfix_take (h: n ≤ m): List.take n l <:+: List.take m l := by
  rw [← Nat.add_sub_of_le h]
  simp only [List.take_add, ge_iff_le, isInfix_append_left]

lemma List.isInfix_drop_of_isInfix_append (h: l₁ <:+: l₂ ++ l₃): l₁.drop (length l₂) <:+: l₃ := by
  have ⟨s, t, ih⟩ := h
  have l₁split := List.take_append_drop (length l₂) l₁
  rw [← l₁split] at ih
  apply_fun List.drop (length l₂) at ih
  simp only [take_append_drop, drop_append_eq_append_drop, ge_iff_le, tsub_le_iff_right,
  drop_length, le_refl, tsub_eq_zero_of_le, nil_append, List.drop, List.length_append, Nat.sub_add_eq] at ih
  suffices drop (length l₂ - length s) l₁ <:+: l₃ by
    apply List.isInfix_trans _ this
    apply List.drop_isInfix_drop
    apply Nat.sub_le
  exists (drop (length l₂) s), (drop (length l₂ - length s - length l₁) t)


@[simp]
lemma Nat.min_self_sub_right (n m: ℕ): min (n) (n-m) = n-m := by
  simp only [ge_iff_le, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le, min_eq_right]

@[simp]
lemma Nat.min_self_sub_left (n m: ℕ): min (n-m) (n) = n-m := by
  rw [min_commutative]
  apply Nat.min_self_sub_right

lemma List.isInfix_take_of_isInfix_append {l₁ l₂ l₃: List α} (h: l₁ <:+: l₂ ++ l₃): l₁.take (length l₁ - length l₃) <:+: l₂ := by
  have ⟨s,t,ih⟩ := h
  have hl: s.length + l₁.length + t.length = l₂.length + l₃.length := by
    apply_fun @List.length α at ih
    simp only [List.length_append] at ih
    exact ih
  
  have l₁split := List.take_append_drop (length l₁ - length l₃) l₁
  rw [←l₁split] at ih
  apply_fun List.take (length l₂) at ih
  simp only [List.take_append_eq_append_take, List.take_take, List.length_take, length_drop, length_append,
    take_length, Nat.sub_self, take_zero, append_nil, Nat.min_self_sub_left] at ih
  have l2len : l₂.length = s.length + l₁.length + t.length - l₃.length := by
    apply Eq.symm
    rw [Nat.sub_eq_of_eq_add]
    exact hl
  rw [l2len, min_eq_right] at ih
  . rw [← ih]
    apply List.isInfix_append_right_of_isInfix
    apply List.isInfix_append_left_of_isInfix
    apply List.isInfix_append_right_of_isInfix
    apply List.isInfix_self
  . rw [Nat.sub_sub, add_comm l₃.length, ← Nat.sub_sub, add_assoc, add_comm, Nat.add_sub_cancel, add_comm]
    simp only [Nat.sub_le_sub_right, le_add_iff_nonneg_left, zero_le]

-- s + l1 + t = l2 + l3
-- l1 + t - l3 
lemma List.singleton_isInfix_iff_mem: [e] <:+: l ↔ e ∈ l := by
  apply Iff.intro
  . intro ⟨s,t,h⟩
    simp only [append_assoc, singleton_append, mem_append, find?, mem_cons, true_or, or_true, ← h]
  . intro mem
    have ⟨s,t,h⟩ := List.mem_split mem
    exists s,t
    rw [h, append_assoc, singleton_append]


set_option maxHeartbeats 0
    

lemma List.splitOnListAux_append [DecidableEq α] (l₁ l₂: List α) (h: ¬ delim <:+: (lastN (length delim -1) l₁) ++ l₂):
    List.splitOnListAux delim (l₁ ++ l₂) #[] #[] h₂ = Array.modifyLast (λ x => x ++ l₂.toArray) (List.splitOnListAux delim l₁ #[] #[] h₂) := by
  cases heq: List.isInfixOf delim (l₁ ++ l₂) with
  | true =>
    rw [List.isInfixOf_ext] at heq
    have ⟨s, lft, rgt⟩ := (List.isInfix_first_match _ _ heq h₂)
    cases List.append_isPrefix_split lft (length l₁) with
    | inl hinf => 
      rw [List.take_append_of_le_length] at hinf <;> simp only [tsub_le_iff_right, ge_iff_le, le_add_iff_nonneg_right, zero_le, nonpos_iff_eq_zero]
      have ⟨t, hinf⟩ := isPrefix_trans hinf take_isPrefix
      rw [← hinf]
      have hrw₁: s ++ delim ++ t ++ l₂ = s ++ delim ++ (t ++ l₂) := by simp only [append_assoc]
      have hrw₂: s ++ delim ++ t = s ++ delim ++ t := by simp only [append_assoc]

      rw [hrw₁, hrw₂, splitOnListAux_progress rgt, splitOnListAux_progress rgt]
      have _ : length t < length l₁ := by
        apply_fun @List.length α at hinf
        rw [← hinf, length_append, length_append]
        apply Nat.lt_add_of_pos_left
        apply Nat.add_pos_right
        apply List.length_pos_of_ne_nil h₂
        
      rw [List.splitOnListAux_append t]
      . apply Array.ext'
        simp only [Array.append_data, Array.data_toArray, Array.modifyLast_data, singleton_append]
        cases h₃: (splitOnListAux delim t #[] #[] h₂).data with
        | nil => 
          exfalso
          apply @splitOnListAux_ne_nil α delim #[] #[] h₂ _ t
          apply Array.ext'
          simp only [h₃, Array.data_toArray]
        | cons head tail=> conv => right; rw [List.modifyLast_cons (List.cons_ne_nil head tail)]
      . rw [← hinf] at h
        intro contr
        apply h
        unfold lastN
        unfold lastN at contr
        rw [List.drop_append_eq_append_drop,List.drop_append_eq_append_drop]
        simp only [append_assoc, length_append, tsub_le_iff_right, ge_iff_le, add_le_add_iff_left]
        apply List.isInfix_append_left_of_isInfix
        apply List.isInfix_append_left_of_isInfix
        convert contr using 3
        rw [ Nat.add_comm (length delim), ← Nat.add_assoc, Nat.add_sub_assoc, Nat.sub_sub_self, ←Nat.sub_sub,
          Nat.add_comm (length s), Nat.add_assoc, Nat.add_comm (length s), ← Nat.add_assoc, Nat.add_sub_assoc, Nat.sub_self,
          Nat.add_zero]
        . rw [Nat.sub_sub_eq_add_sub_of_le]
          apply Nat.succ_le.2
          simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, ne_eq, h₂, not_false_iff, length_pos_of_ne_nil]
        . simp only [le_refl]
        . apply Nat.succ_le.2
          simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, ne_eq, h₂, not_false_iff, length_pos_of_ne_nil]
        . simp only [tsub_le_iff_right, ge_iff_le, le_add_iff_nonneg_right]
      . apply le_refl
    | inr hinf =>
      have hzero: length l₁ + 1 - length delim - length l₁ = 0 := by
        simp only [tsub_le_iff_right, ge_iff_le, add_le_add_iff_left, zero_le, nonpos_iff_eq_zero,
          tsub_eq_zero_iff_le]
        apply Nat.succ_le_of_lt
        simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, ne_eq, h₂, not_false_iff, length_pos_of_ne_nil]
      rw [List.drop_append_eq_append_drop, hzero, drop] at hinf
      have ⟨t, hinf⟩ := hinf
      unfold lastN at h
      exfalso
      apply h
      exists drop (length l₁ + 1 - length delim) s, t
      convert hinf using 3
      rw [Nat.sub_sub_eq_add_sub_of_le]
      apply Nat.succ_le_of_lt
      apply Nat.zero_lt_of_ne_zero
      simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, ne_eq, length_eq_zero, h₂, not_false_iff]

  | false =>
    rw [← Bool.not_eq_true, isInfixOf_ext] at heq
    have not_in_l₁: ¬ delim <:+: l₁  :=  by
      intro contr;
      apply heq
      apply List.isInfix_append_right_of_isInfix contr
    rw [splitOnListAux_nonmatching _ heq, splitOnListAux_nonmatching _ not_in_l₁]
    apply Array.ext'
    simp only [Array.data_toArray, Array.modifyLast_data, modifyLast_singleton, cons.injEq, and_true]
    apply Array.ext'
    simp only [Array.data_toArray, Array.append_data]
termination_by splitOnListAux_append l _ _ => length l

lemma List.map_modifyLast (P: Function.Semiconj f h g): map f (modifyLast h l) = modifyLast g (map f l) := by
  if heq: l = [] then
    simp only [heq, map, modifyLast_nil]
  else
    rw [← List.dropLast_append_getLast heq, List.modifyLast_append_one, map_append, map_append,
      map_singleton, map_singleton,List.modifyLast_append_one, P.eq]

lemma List.map_dropLast: map f (dropLast l) = dropLast (map f l) := by
  simp only [dropLast_eq_take, map_take, length_map]


lemma Int.not_newline_mem_reprΔ: '\n' ∉ Int.reprΔ n := by
  unfold reprΔ
  intro contr
  split at contr
  case h_1 n =>
      have isdig := Nat.toDigits_digits 10 n
      simp only [beq_iff_eq, List.all_eq_true, forall_true_left] at isdig
      have h := isdig '\n' contr
      simp only at h
  case h_2 n =>
    simp only [List.singleton_append, List.find?, List.mem_cons, false_or] at contr
    have isdig := Nat.toDigits_digits 10 (Nat.succ n)
    simp only [beq_iff_eq, List.all_eq_true, forall_true_left] at isdig
    have h := isdig '\n' contr
    simp only at h
  
lemma List.splitOnList_append [DecidableEq α] (l₁ l₂: List α) (h: ¬ delim <:+: (lastN (length delim -1) l₁) ++ l₂):
    List.splitOnList delim (l₁ ++ l₂) = List.modifyLast (λ x => x ++ l₂) (List.splitOnList delim l₁) := by
  unfold splitOnList
  match delim with
  | [] => simp only [modifyLast_singleton]
  | hd::tl => 
    simp only [Array.toList_eq, Array.map_data]
    rw [List.splitOnListAux_append _ _ h]
    rw [← map_modifyLast]
    . rw [Array.modifyLast_data]
    . unfold Function.Semiconj
      simp only [Array.toList_eq, Array.append_data, Array.data_toArray, forall_const]

lemma List.modifyHead_eq_modifyNth (l:List α): List.modifyHead f l = List.modifyNth f 0 l := by
  simp only [modifyNth, modifyHead, modifyNthTail]

lemma List.modifyNth_ge_length (h:(length l) ≤ i): List.modifyNth f i l = l := by
  simp only [modifyNth_eq_set_get?, zero_le, ge_iff_le, nonpos_iff_eq_zero, List.get?_eq_none.2 h,
    Option.map_eq_map, Option.map_none', Option.getD_none]

lemma List.modifyNth_modifyNth_ne (h: i ≠ j): List.modifyNth f i (List.modifyNth g j l) = List.modifyNth g j (List.modifyNth f i l) := by
  if h₁: i < length l then
    if h₂: j < length l then
      rw [List.modifyNth_eq_set_get _ h₁, List.modifyNth_eq_set_get _ h₂, List.modifyNth_eq_set_get, List.modifyNth_eq_set_get, 
        set_comm, get_set_ne, get_set_ne] <;>
        simp only [h, h₁, h₂, ne_eq, not_false_iff,length_set]
      . apply Ne.symm h
      . apply Ne.symm h
    else
      simp only [not_lt] at h₂
      have h₃: length (modifyNth f i l) ≤ j := by simp only [modify_get?_length, h₂]
      rw [modifyNth_ge_length h₂, modifyNth_ge_length h₃]
  else
    simp only [not_lt] at h₁
    have h₃: length (modifyNth g j l) ≤ i := by simp only [modify_get?_length, h₁]
    rw [modifyNth_ge_length h₁, modifyNth_ge_length h₃]


lemma List.set_set (h:i=j): List.set (List.set l j b) i a= List.set l i a := by
  subst j
  apply List.ext_get
  . simp only [length_set]
  . intro n _ _
    repeat rw [List.get_set]
    split <;> simp only

lemma List.modifyNth_modifyNth_eq (h: i=j): List.modifyNth f i (List.modifyNth g j l) = List.modifyNth (f ∘ g) i l := by
  subst h
  if h₁: i < length l then
    rw [List.modifyNth_eq_set_get _ h₁, List.modifyNth_eq_set_get _ h₁, List.modifyNth_eq_set_get,
      List.get_set_eq, set_set, Function.comp_apply] <;>
      simp only [h₁, length_set]
  else
    simp only [not_lt] at h₁
    have h₃: length l ≤ i := by simp only [modify_get?_length, h₁]
    rw [modifyNth_ge_length h₁, modifyNth_ge_length h₃, modifyNth_ge_length h₁]


lemma List.modifyNth_comm_of_comm (P: Function.Commute f g): List.modifyNth f i (List.modifyNth g j l) = List.modifyNth g j (List.modifyNth f i l) := by
  cases heq: decide (i = j) with
  | true =>
    simp only [decide_eq_true_eq] at heq
    rw [List.modifyNth_modifyNth_eq heq, List.modifyNth_modifyNth_eq (Eq.symm heq), P.comp_eq, heq]
  | false =>
    simp only [decide_eq_false_iff_not] at heq
    have heq₂ : j ≠ i := by simp only [ne_eq, ne_comm, heq, not_false_iff]
    rw [List.modifyNth_modifyNth_ne heq, List.modifyNth_modifyNth_ne heq₂]

lemma List.splitOnP_append (h: ∀ e ∈ l₂, ¬P e = true): List.splitOnP P (l₁++l₂) = List.modifyLast (λ x => List.append x l₂) (List.splitOnP P l₁) := by
  induction l₁ with
  | nil => 
    simp only [nil_append, List.append_eq, splitOnP_nil, modifyLast_singleton]
    apply List.splitOnP_eq_single
    apply h
  | cons head tail ih =>
    rw [cons_append, splitOnP_cons, splitOnP_cons]
    split
    case inl heq =>
      rw [ih,modifyLast_cons]
      apply List.splitOnP_ne_nil
    case inr heq =>
      rw [ih, modifyLast_eq_modifyNth, modifyLast_eq_modifyNth,
        modifyHead_eq_modifyNth, modifyHead_eq_modifyNth,
        modifyNth_comm_of_comm]
      simp only [List.append_eq, tsub_le_iff_right, ge_iff_le, zero_le, nonpos_iff_eq_zero, modify_get?_length]
      simp only [Function.Commute, Function.Semiconj, List.append_eq, cons_append, forall_const]
      
lemma List.splitOn_append [BEq α] {l₁ l₂: List α} (h: ∀ e ∈ l₂, ¬ e == delim ): List.splitOn delim (l₁++l₂) = List.modifyLast (λ x => List.append x l₂) (List.splitOn delim l₁) := by
  unfold splitOn
  rw [List.splitOnP_append]
  intro e ein
  exact h e ein

lemma List.modifyHead_append (h:l₁ ≠ []): List.modifyHead f (l₁ ++ l₂) = List.modifyHead f l₁ ++ l₂ := by
  cases l₁ with
  | nil => simp only [ne_eq, not_true] at h
  | cons head tail => simp only [modifyHead, cons_append]

lemma List.splitOnP_last [BEq α] (front: List α) (sep: α) (tail: List α) (h: ∀ e ∈ tail, ¬P e = true) (hsep: P sep = true): List.splitOnP P (front ++ sep :: tail) = List.splitOnP P (front) ++ [tail] := by
  induction front with
  | nil => 
    simp only [nil_append, splitOnP_cons, hsep, modifyHead, ite_true, splitOnP_nil, singleton_append, cons.injEq,
      true_and]
    rw [List.splitOnP_eq_single]
    apply h
  | cons hd tl ih =>
    simp only [cons_append, splitOnP_cons]
    split
    . simp only [ih, cons_append]
    . rw [ih, List.modifyHead_append]
      apply List.splitOnP_ne_nil

lemma List.splitOn_last [BEq α] [LawfulBEq α](front: List α) (sep:α) (tail: List α) (h: ∀ e ∈ tail, ¬ e == sep): List.splitOn sep (front ++ sep :: tail) = List.splitOn sep (front) ++ [tail] := by
  unfold splitOn
  apply List.splitOnP_last
  . exact h
  . simp only [beq_self_eq_true]

@[simp]
lemma WithTop.untop'_min_left [LinearOrder α] (x: α) (y: WithTop α): untop' d (min ↑x y) = min x (untop' x y) := by
  cases y with
  | none => simp only [none_eq_top, ge_iff_le, le_top, min_eq_left, untop'_coe, untop'_top, min_self]
  | some y' => rw [some_eq_coe, ← coe_min, untop'_coe, untop'_coe] 

@[simp]
lemma WithTop.untop'_min_right [LinearOrder α] (x: WithTop α) (y: α): untop' d (min x ↑y) = min (untop' y x) y:= by
  rw [min_comm x, min_comm _ y]
  apply untop'_min_left

lemma List.not_isInfix_intercalate_by_element (l₁ delim :List α) (l₂:List (List α))
 (h: ∀ e ∈ l₂, ¬ l₁ <:+: delim ++ e ++ delim)
 (hlen: length l₁ ≤ 1 + length delim)
 (hne_nil: l₂ ≠ []):
  ¬ l₁ <:+: delim ++ List.intercalate delim l₂ ++ delim:= by
  match hl: l₂ with
  | [] =>  simp only [ne_eq, not_true] at hne_nil
  | [elem] => 
    intro ⟨s,t, heq⟩
    simp [List.intercalate] at heq
    apply h elem (List.mem_singleton_self elem)
    simp [← heq]
    exists s, t
    simp only [append_assoc]
  | head::mid::tail =>
    intro contr
    simp [intercalate, intersperse_cons_cons] at contr
    cases isInfix_split contr (length (delim ++ head ++ delim)) with
    | inl hinf=>
      rw [← append_assoc, ← append_assoc, take_left] at hinf
      apply h head ?_ hinf
      simp only [mem_cons, true_or]
    | inr hinf =>
      
      rw [length_append, length_append, add_assoc, add_assoc,
        ← append_assoc,← append_assoc, ← intercalate, drop_append_eq_append_drop, 
        drop_append_eq_append_drop, drop_length_le, length_append, Nat.sub_sub,
        Nat.add_comm (length l₁), ← Nat.add_assoc, ←Nat.sub_sub, Nat.add_sub_self_left,
        Nat.sub_sub, Nat.add_comm (length l₁),← Nat.sub_sub, length_append,length_append,
        ← Nat.sub_sub, ← Nat.sub_sub, Nat.add_assoc, Nat.add_sub_self_left, Nat.add_sub_self_left,
        Nat.add_sub_self_left] at hinf

      have not_inf := h head (by simp only [mem_cons, true_or])
      have hge: 1 ≤ length l₁ := by 
        apply Nat.succ_le_of_lt ( length_pos_of_ne_nil _)
        intro x; simp [x] at not_inf
      simp only [Nat.sub_eq_zero_of_le hge, tsub_le_iff_right, ge_iff_le, nil_append, drop] at hinf
      have tail_notin :∀ (e : List α), e ∈ mid :: tail → ¬l₁ <:+: delim ++ e ++ delim := by
        intro e ein
        apply h
        rw [mem_cons]; right; exact ein
      apply not_isInfix_intercalate_by_element l₁ delim (mid::tail) tail_notin _
      . simp only [ne_eq, not_false_iff]
      . apply isInfix_trans hinf
        exists take (length delim + 1 - length l₁) delim, []
        rw [← append_assoc, take_append_drop, append_nil, append_assoc]
      . exact hlen
      . simp [length_append, tsub_le_iff_right, ge_iff_le]
        apply Nat.le_sub_of_add_le
        rw [add_assoc]
        apply Nat.add_le_add_left
        apply Nat.add_le_add_left
        rw [add_comm]
        exact hlen


lemma List.isInfix_length {l₁ l₂: List α} (h:l₁<:+: l₂): length l₁ ≤ length l₂ := by
  have ⟨s,t, heq⟩ := h
  apply_fun @length α at heq
  rw [← heq]
  rw [length_append, length_append,  add_comm (length s), add_assoc]
  apply Nat.le_add_right

lemma List.eq_of_isInfix_len_ge {l₁ l₂: List α} (h: l₁ <:+: l₂) (len_ge: length l₁ ≥ length l₂): l₁ = l₂ := by
  have ⟨s, t, heq⟩ := h
  have len_sum_eq := congr_arg length heq
  simp only [append_assoc, length_append] at len_sum_eq
  rw [add_comm (length l₁), add_comm, add_comm (length t), add_assoc] at len_sum_eq
  have len_eq : length l₁ = length l₂ := by
    apply ge_antisymm len_ge
    rw [← len_sum_eq]
    apply Nat.le_add_right
  rw [len_eq] at len_sum_eq
  simp only [add_right_eq_self, zero_le, ge_iff_le, nonpos_iff_eq_zero, add_eq_zero_iff] at len_sum_eq
  have ⟨teq, seq⟩ := len_sum_eq
  rw [List.length_eq_zero] at seq
  rw [List.length_eq_zero] at teq
  subst_vars
  simp only [append_nil, nil_append]

lemma List.mem_intersperse (h:a ∈ intersperse sep l): a = sep ∨ a ∈ l := by
  match l with
  | [] => rw [intersperse] at h; contradiction
  | [single] =>
    simp only [intersperse, mem_singleton] at h
    right
    simp only [h, mem_singleton]
  | head::mid::tail =>
    simp only [intersperse, mem_cons] at h
    simp only [mem_cons]
    rcases h with hd | sp | mem
    . simp only [hd, true_or, or_true]
    . simp only [sp, true_or]
    . rcases mem_intersperse mem with mid | tl
      . simp only [mid, true_or]
      . simp only [mem_cons] at tl
        simp only [tl, or_true]

lemma List.mem_intersperse_of_mem (h: a ∈ l): a ∈ intersperse sep l :=  by
  match l with
  | [] => simp only [not_mem_nil] at h
  | [a] => simp_all only [mem_singleton, intersperse]
  | head::mid::tail =>
    simp only [intersperse, mem_cons]
    simp at h
    rcases h with h |m |t <;> simp_all
    . right; right; apply mem_intersperse_of_mem; simp only [mem_cons, true_or]
    . right; right; apply mem_intersperse_of_mem; simp only [t, mem_cons, or_true]



lemma List.mem_intercalate (h:a ∈ intercalate delim l): a ∈ delim ∨ ∃ e∈l, a ∈ e := by
  simp only [intercalate, mem_join] at h
  have ⟨e, ein, ain⟩ := h
  cases List.mem_intersperse ein with
  | inl heq =>
    simp only [← heq, ain, true_or]
  | inr heq =>
    right
    exists e

lemma List.mem_intercalate_of_mem (h₁: a ∈ e) (h₂: e ∈ l): a ∈ intercalate delim l := by
  rw [intercalate]
  apply mem_join_of_mem
  apply mem_intersperse_of_mem
  apply h₂
  apply h₁

lemma List.join_eq_nil (h: join l = []): ∀ e ∈ l, e = [] := by
  induction l with
  | nil =>
    simp only [not_mem_nil, IsEmpty.forall_iff, forall_const]
  | cons head tail ih=>
    simp_all only [join, append_eq_nil, mem_cons, forall_eq_or_imp, true_and, forall_true_left]
    apply ih

lemma List.intercalate_eq_nil (h: intercalate delim l = []): ∀ e ∈ l, e = [] := by
  rw [intercalate] at h
  have all_nil := join_eq_nil h
  intro e ein
  apply all_nil
  apply mem_intersperse_of_mem ein


lemma List.getLast_intercalate {a:α} (l:List (List α)) (h₂: intercalate delim l ≠ []) (not_nil: l.getLast? ≠ some []): 
    getLast (intercalate delim l) h₂ =
    getLast (getLast l (by intro contr; apply h₂; rw [contr]; simp only [intercalate._eq_1, join])) (by intro contr; apply not_nil;rw[←contr]; apply List.getLast?_eq_getLast)
    := by
  match l with
  | [] => simp only [intercalate._eq_1, join, ne_eq, not_true] at h₂
  | [a] =>
    simp [intercalate]
  | [a,b] =>
    simp [intercalate]
    simp [← intercalate._eq_1]
    simp only [← append_assoc]
    rw [getLast_append']
  | head::mid::mid₂::tail =>
    simp [intercalate]
    simp [← intercalate._eq_1]
    simp only [← append_assoc]
    rw [getLast_append', getLast_intercalate (mid₂::tail)]
    . intro contr
      apply not_nil
      rw [List.getLast?_eq_getLast]
      simp only [ne_eq, not_false_iff, getLast_cons, Option.some.injEq]
      generalize_proofs hp
      apply List.intercalate_eq_nil contr (getLast (mid₂ :: tail) hp)
      apply List.getLast_mem
      simp only [ne_eq, not_false_iff]
    . intro contr
      apply not_nil
      simp only [getLast?_cons_cons, contr]
    . exact a



lemma List.mem_of_mem_take (n) (h:a ∈ take n l): a ∈ l := by
  rw [← take_append_drop n l]
  apply mem_append_left _ h
  
@[simp]
lemma List.countp_nil: countp p [] = 0 := by
  unfold countp countp.go
  rfl

lemma List.countp.go_acc: List.countp.go p l acc = acc + List.countp.go p l 0 := by
  induction l generalizing acc with
  | nil => unfold go; simp
  | cons head tail ih =>
    unfold go
    cases p head with
    | true => simp only [@ih (acc + 1), add_assoc, zero_le, ge_iff_le, nonpos_iff_eq_zero, cond_true, zero_add, @ih 1]
    | false => simp only [@ih acc, zero_le, ge_iff_le, nonpos_iff_eq_zero, cond_false, zero_add]


lemma List.countp_cons (head:α) (tail: List α): countp p (head::tail) = (if p head then 1 else 0) + countp p tail := by
  rw [countp, countp.go]
  cases p head with
  | true => simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, zero_add, cond_true, ite_true]; rw [List.countp.go_acc, ← countp]
  | false => simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, zero_add, cond_false, ite_false]; rw [← countp]

@[simp]
lemma List.count_nil [BEq α] (a: α): count a [] = 0 := by
  unfold count
  apply countp_nil

lemma List.count_cons [BEq α] (head:α) (tail: List α): count a (head::tail) = (if head == a  then 1 else 0) + count a tail := by
  unfold count
  apply countp_cons

@[simp]
lemma List.countp_append: countp p (l₁ ++ l₂) = countp p l₁ + countp p l₂ := by
  induction l₁ with
  | nil => simp only [nil_append, countp_nil, zero_le, ge_iff_le, nonpos_iff_eq_zero, zero_add]
  | cons head tail ih => simp only [cons_append, countp_cons, ih, zero_le, ge_iff_le, nonpos_iff_eq_zero, add_assoc]

@[simp]
lemma List.count_append [BEq α] (a: α) (l₁ l₂: List α): count a (l₁ ++ l₂) = count a l₁ + count a l₂ := by
  unfold count
  apply List.countp_append


lemma List.isInfix_countp_le (h: l₁ <:+: l₂): countp p l₁ ≤ countp p l₂ := by
  have ⟨s,t,heq⟩ := h
  apply_fun countp p at heq
  simp only [append_assoc, countp_append] at heq
  rw [← heq]
  linarith

lemma List.isInfix_count_le [BEq α] (a) {l₁ l₂: List α} (h: l₁ <:+: l₂): count a l₁ ≤ count a l₂ := by
  unfold count
  apply List.isInfix_countp_le h

lemma List.count_pos_iff_mem [BEq α] [LawfulBEq α] (a: α) (l: List α): count a l > 0 ↔ a ∈ l := by
  apply Iff.intro
  . intro count_pos
    induction l with
    | nil => simp only [count_nil, zero_le, ge_iff_le, nonpos_iff_eq_zero, lt_self_iff_false] at count_pos
    | cons head tail ih=>
      simp only [count_cons, beq_iff_eq, zero_le, ge_iff_le, nonpos_iff_eq_zero, gt_iff_lt, add_pos_iff] at count_pos
      cases count_pos with
      | inl hlt =>
        split at hlt
        case inl heq => simp at heq;  simp [heq]
        case inr heq => simp only at hlt
      | inr hlt =>
        apply mem_cons.2; right
        apply ih hlt
  . intro ain
    induction l with
    | nil => simp only [not_mem_nil] at ain
    | cons head tail ih => 
      cases mem_cons.1 ain with
      | inl heq =>
        simp only [heq, count_cons, beq_self_eq_true, ite_true, zero_le, ge_iff_le, nonpos_iff_eq_zero, gt_iff_lt,
          add_pos_iff, true_or]
      | inr hin =>
        simp only [count_cons, beq_iff_eq, zero_le, ge_iff_le, nonpos_iff_eq_zero, gt_iff_lt, add_pos_iff, ih hin, or_true]


lemma List.splitOnList_intercalate [DecidableEq α] {delim: List α} {l: List (List α)} (h: ∀ e ∈ l, ¬ delim <:+: (e++delim.dropLast)) (h₂: l ≠ []):
    List.splitOnList delim (List.intercalate delim l) = l := by
  induction l with
  | nil => 
    contradiction
  | cons head tail ih=>
    cases delim
    case nil =>
      simp only [find?, mem_cons, dropLast, append_nil, nil_isInfix, not_true, forall_eq_or_imp, false_and] at h head
    case cons dhead dtail=>
      unfold intercalate
      cases h₂:tail with
      | nil => 
        subst tail
        simp only [join, append_nil]
        apply List.splitOnList_nonmatching
        have h₃ := (h head (List.mem_singleton_self _))
        intro ⟨s,t, hcontr⟩
        apply h₃
        exists s, (t ++ dropLast (dhead :: dtail))
        simp only [append_assoc, cons_append, ← hcontr]
      | cons mid tail₂ =>
        simp only [join]
        rw [← List.append_assoc, List.splitOnList_progress, ← List.intercalate, ← h₂, ih]
        . simp only [singleton_append]
        . intro e ein
          apply h
          subst h₂
          simp_all only [find?, mem_cons, ne_eq, not_false_iff, or_true, implies_true, forall_const, forall_true_left,
            forall_eq_or_imp]
        . simp only [h₂, ne_eq, not_false_iff]
        . intro contr
          apply h head
          apply List.mem_cons_self
          exact contr


def elfToString (e: List Int): List Char :=
  List.intercalate ['\n'] (List.map Int.reprΔ e)

def elvesToString (elves: List (List Int)) : List Char := 
  if elves == [] then
    []
  else
    List.intercalate ['\n','\n'] (List.map elfToString elves) ++ ['\n']

def stringToElf (s: List Char): List Int :=
  List.splitOn '\n' s
    |> List.filter (λ x => x ≠ [])
    |> List.map String.toIntΔ

def stringToElves (s: List Char) : List (List Int) :=
  if s == [] then
    []
  else
    s
      |> List.splitOnList ['\n', '\n']
      |> List.map stringToElf

@[inline]
abbrev convIf {α} (P : Prop) (_ : Decidable P) (x : P → α) (y : ¬P → α) : α := if h : P then x h else y h

def convIf.rhs {α} (P : Prop) [inst : Decidable P] (a : α) := convIf P inst (λ _ => a) (λ _ => a)

theorem convIf.id {α} (P : Prop) [inst : Decidable P] (a : α) : a = convIf P inst (λ _ => a) (λ _ => a) :=
by
  simp[convIf]; done

open Lean.Parser.Tactic.Conv
syntax (name := conv_if) "if" ident ":" term  "then" convSeq "else" convSeq : conv

open Lean.Elab Tactic Conv in
@[tactic conv_if]
def convIfTactic : Tactic
| `(conv| if $h : $P then $trueConv else $falseConv) => do
   withMainContext do

     let p ← elabTerm P none
     let t' ← Lean.Meta.mkAppM ``convIf.rhs #[p, (← getLhs)]
     let h' ← Lean.Meta.mkAppM ``convIf.id  #[p, (← getLhs)]

     updateLhs t' h'
     evalTactic (←
       `(convSeq| unfold convIf.rhs
                  conv => enter[3]; intro $h; ($trueConv)
                  conv => enter[4]; intro $h; ($falseConv)))
| _ => throwUnsupportedSyntax

lemma double_newline_not_isInfix_stringToElf (elf: List Int): ¬ ['\n', '\n'] <:+: elfToString elf := by
  if hempty: elf = [] then
    intro contr
    have contr := List.isInfix_length contr
    simp only [List.length_cons, List.length_singleton, elfToString, hempty,
      List.map] at contr
  else
    unfold elfToString
    intro contr
    apply List.not_isInfix_intercalate_by_element  ['\n', '\n']  ['\n'] (List.map Int.reprΔ elf)
    . simp only [List.mem_map', forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro a _ contr₂
      cases List.isInfix_append_split_right contr₂ with
      | inl h₁ =>
        cases List.isInfix_append_split_left h₁ with
        | inl h₂ =>
          have h₃ := List.isInfix_drop_of_isInfix_append h₂
          simp only [List.drop, List.singleton_isInfix_iff_mem] at h₃
          apply Int.not_newline_mem_reprΔ h₃
        | inr h₄ =>
          simp only [List.length_cons, List.length_singleton, ge_iff_le, Nat.succ_sub_succ_eq_sub, tsub_zero,
            List.singleton_append, List.lastN_one_eq_getLast, List.take, List.length,List.getLast?_cons] at h₄
          rw [Option.to_list_some] at h₄
          have newline_in_repr := List.isInfix_take_of_isInfix_append h₄
          simp only [List.take, List.singleton_isInfix_iff_mem, List.mem_singleton] at newline_in_repr
          rw [List.getLastD_ne_nil] at newline_in_repr
          apply Int.not_newline_mem_reprΔ (n:=a)
          rw [newline_in_repr]
          apply List.getLast_mem
          apply Int.reprΔ_ne_nil a
      | inr h₅ =>
        have hlen := List.isInfix_length h₅
        simp only at hlen
    . simp only
    . simp only [ne_eq, List.map_eq_nil, hempty, not_false_iff]
    . apply List.isInfix_append_right_of_isInfix 
      apply List.isInfix_append_left_of_isInfix 
      exact contr
      

lemma newline_not_last_elfToString (elf: List ℤ): List.getLast? (elfToString elf) ≠  some '\n' := by
  if hnil: elf = [] then
    simp only [hnil, ne_eq]
  else
    unfold elfToString
    intro contr
    have h₂ := List.getLast?_some contr
    rw [List.getLast_intercalate] at h₂
    . simp only [List.getLast_map _ hnil] at h₂
      revert h₂
      generalize_proofs hnil'
      intro h₂
      have mem := List.getLast_mem hnil'
      rw [h₂] at mem
      apply Int.not_newline_mem_reprΔ
      apply mem
    . intro contr
      have gl := List.getLast?_some contr
      rw [List.getLast_map] at gl
      apply Int.reprΔ_ne_nil
      apply gl
      apply hnil
    . exact '\n'
  
 

lemma stringToElf_ignoresTrailing (s: List Char): stringToElf (s ++ ['\n']) = stringToElf s := by
  simp only [stringToElf, ne_eq, decide_not, List.find?, List.not_mem_nil, beq_iff_eq, IsEmpty.forall_iff,
    forall_const, List.splitOn_last, List.filter_append, decide_True, Bool.not_true, not_false_iff,
    List.filter_cons_of_neg, List.filter_nil, List.append_nil]

@[simp]
lemma List.intercalate_singleton (sep elem: List α): List.intercalate sep [elem] = elem := by
  rw [List.intercalate, List.intersperse_singleton, List.join_cons, List.join_nil, List.append_nil]

lemma elfToString_roundtrip (elf:List Int): stringToElf (elfToString elf) = elf := by
  if h:elf = [] then
    simp only [h]
  else
    unfold stringToElf elfToString
    rw [List.splitOn_intercalate, List.filter_eq_self.2, List.map_map]
    . unfold Function.comp
      simp only [String.toIntΔ_inv_IntreprΔ, List.map_id'']
    . simp only [List.mem_map', ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂, Int.reprΔ_ne_nil, not_false_iff, implies_true, forall_const]
    . simp only [List.mem_map', forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro a _
      apply Int.not_newline_mem_reprΔ
    . simp only [ne_eq, List.map_eq_nil, h, not_false_iff]

theorem elves_roundtrip (elves: List (List Int)): stringToElves (elvesToString elves) = elves := by
  induction elves with
  | nil => simp only
  | cons hd tail ih =>
    unfold elvesToString stringToElves
    cases tail with
    | nil =>
      simp only [beq_iff_eq, List.map, List.intercalate_singleton, ite_false, List.append_eq_nil, and_false]
      rw [List.splitOnList_nonmatching, List.map_singleton, stringToElf_ignoresTrailing, elfToString_roundtrip]
      intro contr
      cases List.isInfix_append_split_left contr with
      | inl h₁ =>
        apply double_newline_not_isInfix_stringToElf hd h₁
      | inr h₂ =>
        simp only [List.length_cons, List.length_singleton, ge_iff_le, Nat.succ_sub_succ_eq_sub, tsub_zero] at h₂
        have newline_in_elf := List.isInfix_take_of_isInfix_append h₂
        simp only [List.take, List.length_nil, zero_add, ge_iff_le, List.lastN_one_eq_getLast,List.singleton_isInfix_iff_mem, Option.mem_toList, Option.mem_def] at newline_in_elf
        apply newline_not_last_elfToString _ newline_in_elf  
    | cons mid tl =>
      simp only [beq_iff_eq, List.map, List.map_eq_nil, IsEmpty.forall_iff,
        List.join, ite_false, List.append_eq_nil, and_false, List.intercalate]
      rw [List.append_assoc, List.append_assoc, ← List.append_assoc, List.splitOnList_progress, List.map_append, 
        List.map_singleton, elfToString_roundtrip, List.singleton_append, ←ih, stringToElves, elvesToString, List.intercalate]
      . simp only [List.map_eq_nil, beq_iff_eq, List.map, ite_false, List.append_eq_nil, and_false]
      . simp only [List.dropLast]
        intro contr
        cases List.isInfix_append_split_left contr with
        | inl h₃ =>
          apply double_newline_not_isInfix_stringToElf hd
          apply h₃
        | inr h₄ =>
          simp only [List.length_cons, List.length_singleton, ge_iff_le, Nat.succ_sub_succ_eq_sub, tsub_zero, List.length_nil] at h₄
          have last_contains := List.isInfix_take_of_isInfix_append h₄
          simp only [List.take, ge_iff_le, List.lastN_one_eq_getLast, List.singleton_isInfix_iff_mem, Option.mem_toList, Option.mem_iff] at last_contains
          apply newline_not_last_elfToString _ last_contains
      
  
def solveOneModel (elves: List (List Int)): Int :=
  elves |>
    List.map List.sum |>
    List.maximum |>
    WithBot.unbot' 0

def solveOne (input: List Char): Int :=
  input |> stringToElves |> solveOneModel

def isSolutionModel (f: (List (List Int))-> Int):= ∀ (elves: List (List Int)), ∀ elf ∈ elves, f elves ≥ List.sum elf

def isSolution f := isSolutionModel (f ∘ elvesToString)

theorem isSolutionModel_solveOneModel: isSolutionModel solveOneModel := by
  unfold isSolutionModel
  intro elves elf elfin
  unfold solveOneModel
  have hsumin: List.sum elf ∈ (List.map List.sum) elves := by apply List.mem_map'.2; exists elf
  have z:=  List.le_maximum_of_mem' hsumin
  apply WithBot.coe_le_coe.1
  apply le_trans z
  apply WithBot.le_coe_unbot'

theorem isSolution_solveOne: isSolution solveOne := by
  unfold isSolution solveOne
  simp [Function.comp, isSolutionModel_solveOneModel, elves_roundtrip]

