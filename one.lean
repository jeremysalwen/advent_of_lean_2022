import Lean
import Mathlib.data.list.basic
import Mathlib.Tactic.Find
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.applyFun
import Init.Data.String.Basic
import Init.Data.Int.Basic
import Std.Data.Array.Init.Lemmas
import Std.Data.List.Init.Lemmas
import Std.Data.Nat.Lemmas
import Std.Data.Int.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Aesop


open Lean Parsec

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
String.toNatΔ (head::tail) = 
  (head.toNat - '0'.toNat)*10^(List.length tail) + (String.toNatΔ tail) := by
  unfold String.toNatΔ
  conv => left; unfold  String.toNatAux
  rw [String.toNatAux_accumulates]
  ring

def String.toIntΔ (s: List Char): ℤ :=
  match s with
  | [] => 0
  | h::tail => if h = '-' then - String.toNatΔ tail else String.toNatΔ (h::tail)

def Int.reprΔ (i: ℤ): List Char :=
  match i with
  | Int.ofNat m => Nat.toDigits 10 m
  | Int.negSucc m => ['-'] ++ Nat.toDigits 10 (Nat.succ m)


theorem Nat.toDigitsCore_nonempty (P: f > n): Nat.toDigitsCore b f n a ≠ [] := by
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

lemma Nat.toDigits_nonempty: Nat.toDigits b n ≠ [] := by
  unfold Nat.toDigits
  simp [Nat.toDigitsCore_nonempty]

@[simp]
lemma Nat.digitChar_is_digit (n: ℕ) (P: n < 10): Char.isDigit (Nat.digitChar n) = true := by
  revert n
  decide

lemma Nat.ne_zero_gt_zero (n:ℕ): n ≠ 0 → n > 0 := by
  intro h
  cases n
  . contradiction
  . simp only [succ_pos'] 

lemma Nat.gt_zero_ne_zero (n:ℕ): n > 0 → n ≠ 0 := by
  intro h
  cases n
  . contradiction
  . simp only [ne_eq, succ_ne_zero, not_false_iff]

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
            . simp [h₅, Nat.ne_zero_gt_zero]
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
                  . apply Nat.ne_zero_gt_zero; intro h; simp only [gt_iff_lt, h, Nat.zero_div, not_true] at *
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
            n ≥ n / b + 1 := by simp only [add_lt_add_iff_right]; apply Nat.div_lt_self; apply Nat.ne_zero_gt_zero; intro h; simp only [gt_iff_lt, h, Nat.zero_div, not_true] at *; apply Q


lemma Nat.toDigits_digits (b: ℕ) (n:ℕ) (P: b <= 10) (Q: b > 1): List.all (Nat.toDigits b n) (Char.isDigit) == true := by
  let h:  ∀ c, c ∈ Nat.toDigitsCore b (n+1) n [] → Char.isDigit c = true ∨ c ∈ [] := by
    intro c
    apply Nat.toDigitsCore_digits  _ _ P Q 
  simp
  simp at h
  unfold Nat.toDigits
  apply h

theorem List.get?_cons {h: α} {tail : List α} {n : Nat} (hn: n>0): (h::tail).get? n = tail.get? (n-1) := by
  conv => left; unfold List.get?
  cases n with
  | zero => simp only at hn
  | succ n => simp only [ge_iff_le, Nat.succ_sub_succ_eq_sub, nonpos_iff_eq_zero, tsub_zero]

@[simp]
theorem List.getD_singleton {n : Nat} (elem: α): List.getD [elem] n elem = elem := by
  unfold getD get? Option.getD
  simp only [cons.injEq, and_imp, forall_apply_eq_imp_iff', forall_eq']
  cases n
  . simp only
  . simp only [get?]

set_option profiler true
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
  List.nil_append, List.getD_singleton]
    
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
      . simp only [ne_eq, h, not_false_iff, ne_zero_gt_zero]
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
            apply Nat.ne_zero_gt_zero
            apply heq
        . exact h
        . exact []
        . calc
          l ≥ n := by exact le_of_lt_succ R
          _ > n/b := h
        . simp

theorem Nat.toDigits_length_eq_log  {b n: ℕ} (P: b>1): List.length (Nat.toDigits b n) = Nat.log b n + 1:= by
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
theorem List.take_nil (n) : List.take n ([]:List α) = [] := by 
  unfold take
  split <;> simp at *  

@[simp]
theorem List.lastN_length_eq_self (l: List α): List.lastN (length l) l = l := by
  unfold List.lastN
  simp

#find Nat.min _ _
@[simp]
theorem List.lastN_length (l: List α) (i:ℕ): length (List.lastN i l) = min i (length l) := by
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
  


@[simp]
theorem List.lastN_ge_length (l: List α) (h: n ≥ length l): List.lastN n l = l := by
  unfold List.lastN
  simp [h]

@[simp]
lemma Nat.eq_of_le_ge {n m: ℕ} (P: n ≤ m) (Q: n ≥ m): n = m := by
  have R:= Nat.eq_or_lt_of_le P
  cases R
  . assumption
  . have M:= Nat.not_lt_of_le Q;  contradiction

@[simp]
theorem List.get_zero' (l:List α) (h: 0 < l.length): List.get l {val:=0, isLt:=h} :: List.tail l = l := by
  cases l with
  | nil => simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, length_nil, lt_self_iff_false] at h
  | cons => simp only [get, tail_cons]

@[simp]
theorem List.drop_one_eq_tail (l:List α): l.drop 1 = l.tail := by
  induction l <;> simp

@[simp]
theorem List.drop_eq_cons (i) (l: List α) (h: i < l.length): l[i] :: l.drop (i+1) = l.drop i := by
  induction l generalizing i with
  | nil => simp only [length_nil, zero_le, ge_iff_le, nonpos_iff_eq_zero, not_lt_zero'] at h
  | cons head tail ih =>
    conv => right; unfold drop
    split
    . next => simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, getElem_eq_get, get, drop]
    . next heq=> 
      simp only at heq
    . next z x n hd tl heq=>
      simp only [cons.injEq] at heq
      have ⟨ _,heq₂⟩ := heq
      rw [ ←heq₂]
      apply ih


lemma reverse_index_valid (n) (k) (P:n<k): k-1-n < k := by 
  rw [Nat.sub_sub]
  apply Nat.sub_lt_self
  . simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, add_pos_iff, true_or]
  . apply Nat.le_of_lt_succ
    rw [Nat.succ_eq_add_one, Nat.add_comm]
    simp only [add_lt_add_iff_right, P]

@[simp]
theorem List.drop_eq_cons_drop (n) (l:List α) (h:n < length l):
  (List.get l ⟨n, h⟩ ) :: (List.drop (n+1) l) = List.drop n l := by
  induction l generalizing n
  . case nil => simp only [length_nil, zero_le, ge_iff_le, nonpos_iff_eq_zero, not_lt_zero'] at h
  . case cons head tail ih =>
    cases n with
    | zero => simp only [get, drop]
    | succ n => simp only [get, drop, zero_le, ge_iff_le, nonpos_iff_eq_zero, Nat.add_eq, add_zero, ih]

@[simp]
theorem List.lastN_eq_cons_lastN (n) (l:List α) (P:n < l.length): 
get l ⟨ l.length - 1 - n, reverse_index_valid n l.length P⟩::(List.lastN n l) = List.lastN (n+1) l := by
  unfold lastN
  have h:  length l - (n + 1) < length l := by
    apply Nat.sub_lt_self
    . simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, add_pos_iff, or_true]
    . simp only [Nat.succ_eq_add_one, P, Nat.succ_le_of_lt]

  conv => 
    right
    rw [← List.drop_eq_cons_drop (h:=h)]

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
theorem List.take_cons (n) (head:α) (tail:List α): List.take (n+1) (head::tail) = head::(List.take n tail) := by
  simp only [take, zero_le, ge_iff_le, nonpos_iff_eq_zero, Nat.add_eq, add_zero]

@[simp]
theorem List.drop_cons (n) (head:α) (tail:List α): List.drop (n+1) (head::tail) = List.drop n tail := by
  simp only [drop, zero_le, ge_iff_le, nonpos_iff_eq_zero, Nat.add_eq, add_zero]

@[simp]
theorem List.take_append (n) (l₁ l₂:List α) (P:n ≤ l₁.length): List.take n (l₁++l₂) = List.take n l₁ := by
  induction l₁ generalizing n with
  | nil =>
    simp_all only [length_nil, zero_le, ge_iff_le, nonpos_iff_eq_zero, nil_append,zero_le, ge_iff_le, nonpos_iff_eq_zero, take]
  | cons head tail ih =>
    cases n with
    | zero =>
      simp only [take]
    | succ n =>
      simp only [take, List.append_eq, cons.injEq, true_and]
      rw [ih]
      simp only [length_cons] at P
      rw [← Nat.succ_le_succ_iff]
      apply P
      
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
      rw [List.take_append]
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
theorem Nat.toDigits_zero (b:ℕ): Nat.toDigits b 0 = ['0'] := by
  unfold toDigits toDigitsCore
  simp only [_root_.zero_le, ge_iff_le, nonpos_iff_eq_zero, Nat.zero_div, zero_mod, ite_true, List.cons.injEq]

theorem Nat.toDigits_modulo (b n p i:ℕ) (P: i<p) (Q: b>1): 
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

theorem List.getD_ext (P: List.length a = List.length b) (Q: ∀ i, List.getD a i d = List.getD b i d): a = b := by
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

theorem  List.getD_eq_get (P:i < List.length l): List.getD l i d = l[i] := by
  unfold getD
  simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, List.get?_eq_get P, Option.getD_some, getElem_eq_get]

theorem List.getD_eq_default (P: i≥ List.length l): List.getD l i d = d := by
  simp only [getD_eq_get?, zero_le, ge_iff_le, nonpos_iff_eq_zero, P, List.get?_eq_none.2, Option.getD_none]

theorem List.getD_reverse (P: i < List.length l): List.getD (List.reverse l) i d = l[(List.length l - 1 - i)]'(Nat.sub_one_sub_lt P) := by
  unfold List.getD
  rw [List.get?_reverse, List.get?_eq_get]
  simp only [tsub_le_iff_right, ge_iff_le, Option.getD_some, getElem_eq_get]
  . exact Nat.sub_one_sub_lt P
  . exact P

@[simp]
theorem List.getD_append (P: i < List.length l₁): List.getD (l₁ ++ l₂) i d = List.getD l₁ i d:= by
  unfold getD
  simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, gt_iff_lt, P, get?_append]


@[simp]
theorem List.getD_append_right (P: i ≥ List.length l₁): List.getD (l₁ ++ l₂) i d = List.getD l₂ (i - List.length l₁) d:= by
  unfold getD
  simp only [zero_le, ge_iff_le, nonpos_iff_eq_zero, gt_iff_lt, P, get?_append_right]


theorem String.toNatΔ_eq_of_rev_get_eq_aux (P: ∀ i, List.getD a.reverse i '0' = List.getD b.reverse i '0') (Q: List.length a ≤ List.length b): String.toNatΔ a = String.toNatΔ b := by
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
                rw [List.getD_append_right, ←R, List.getD_singleton, List.getD_eq_default] <;> 
                  simp only [List.length_reverse, ge_iff_le, h]
            . apply Nat.le_of_lt_succ
              apply Nat.lt_of_le_of_ne Q heq
          . simp only [List.length_cons, Nat.lt_succ_self]

        . simp only [List.length_cons] at Q
          simp only [List.length_reverse, ge_iff_le]
          apply Nat.le_of_lt_succ
          apply Nat.lt_of_le_of_ne Q heq
          

theorem String.toNatΔ_eq_of_rev_get_eq (P: ∀ i, List.getD a.reverse i '0' = List.getD b.reverse i '0'): String.toNatΔ a = String.toNatΔ b := by
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
theorem List.getD_take (P: i < n): List.getD (List.take n l) i d = List.getD l i d := by
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
      
theorem String.toNatΔ_inv_NattoDigits_tail (b n i:ℕ) (Q: b > 1): String.toNatΔ (List.lastN i (Nat.toDigits b n)) = String.toNatΔ (Nat.toDigits b (n % b^i)) := by
  apply String.toNatΔ_eq_of_rev_get_eq
  intro ind
  simp only [ge_iff_le, List.lastN_eq_reverse_take, List.reverse_reverse]
  cases i
  case  zero =>
    simp only [List.take, List.length_nil, zero_le, ge_iff_le, nonpos_iff_eq_zero, List.getD_eq_default,
  Nat.zero_eq, pow_zero, Nat.mod_one, Nat.toDigits_zero, List.reverse_cons, List.reverse_nil, List.nil_append,
  List.length_singleton, List.getD_singleton]
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




    
theorem Nat.toDigits_single_digit (b:ℕ) (n:ℕ) (P: n<b): Nat.toDigits b n = [Nat.digitChar n] := by
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
        . next heq => simp only [Nat.toDigits_nonempty] at heq
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
              . apply Nat.ne_zero_gt_zero
                intro hp
                apply Nat.toDigits_nonempty (List.length_eq_zero.1 hp)
              
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
      simp only [Nat.toDigits_nonempty] at heq
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

def List.splitOnP2 (P: α → Bool) (xs: List α): List (List α) :=
  match xs with
  | [] => [[]] 
  | head::tail => if P head then [] :: List.splitOnP2 P tail else List.modifyHead (cons head) (List.splitOnP2 P tail)


@[simp]
lemma List.splitOnP_nil: List.splitOnP P [] = [[]] := by
  unfold splitOnP
  unfold splitOnP.go
  simp only [Array.toList_eq, Array.data_toArray, Array.toListAppend_eq, nil_append]


lemma foo (a b: Array _): { data := Array.data a ++ (Array.data b ++ [Array.data c]) : Array (List _)} = a ++ (b ++ [Array.data c]) := by
  congr; simp



lemma List.splitOnP.go_ind (xs: List α) (acc: Array α) (init: Array (List α)) (r: Array (List α)): splitOnP.go P xs acc (init ++ r) = init.toList ++ splitOnP.go P xs acc r := by
  revert acc init r
  induction xs with
  | nil => unfold go; simp
  | cons head tail ih => intros acc init r; unfold go; cases (P head) with
    | false => simp [Array.push, ih]
    | true =>
      simp [Array.push]
      have h₂ : (a b: Array (List _)) → (c: Array _) → { data := Array.data a ++ (Array.data b ++ [Array.data c]) : Array (List α)} = a ++ (b ++ [Array.data c]) := by intros; congr; simp
      rw [h₂, ih]; congr; simp; rw [← Array.appendList_data]
  
def Array.modifyHead (F: α→ α) (a:Array α): Array α :=
  Array.modify a 0 F


lemma array_list_split1: { data := [[]] : Array (List α)} = #[[]] ++ #[] := by
 congr


lemma bar (a: α → β → γ): a b = (λx => a b x) := by simp
lemma List.splitOnP.go_acc (xs: List α) (inita: List α) (acc: Array α): splitOnP.go P xs (inita.toArray ++ acc) #[] = List.modifyHead (List.append inita) (List.splitOnP.go P xs acc #[]) := by
  revert inita acc
  induction xs with
  | nil => unfold go; simp
  | cons head tail ih => intros inita acc; unfold go; cases (P head) with
    | false =>
      simp [Array.push, array_list_split1]
      rw [← List.modifyHead ]
      conv in (fun a ↦ inita ++ a) =>
        intro a; rw [← List.append_eq_append]
      conv =>
        right
        left
        rw [← bar]
      rw [←ih]
      congr; simp
    | true =>
      simp [Array.push]
      have h₁: { data := [inita ++ acc.data] : Array (List α)} = #[inita ++ acc.data] ++ #[] := by congr
      have h₂: { data := [acc.data] } = #[acc.data] ++ #[]:= by congr
      rw [h₁, h₂, List.splitOnP.go_ind, List.splitOnP.go_ind]
      simp

lemma doo: { data := [[]] : Array (List α)} = #[[]] ++ #[] := by
 congr

lemma List.splitOnP_eq_splitOnP2: List.splitOnP P xs = List.splitOnP2 P xs := by
  induction xs with
  | nil => unfold splitOnP2; simp
  | cons h tail ih => 
    unfold splitOnP2 splitOnP splitOnP.go
    cases P h with
      | true => 
        simp [Array.push, doo, List.splitOnP.go_ind]
        rw [← splitOnP]
        apply ih
      | false => 
        simp [Array.push]
        have h₁:  { data := [h] } = #[h] ++ #[] := by congr
        rw [h₁, List.splitOnP.go_acc, ←List.splitOnP, ←ih]
        simp

@[simp]
lemma List.splitOnP_nonempty: List.splitOnP P xs ≠ [] := by
  rw [List.splitOnP_eq_splitOnP2]
  induction xs with
  | nil =>
    unfold splitOnP2
    simp
  | cons h t ih =>
    unfold splitOnP2
    split
    . simp
    . simp
      split
      . contradiction
      . simp

theorem List.splitOnP_all_false (h: ∀ e ∈ xs, P e = false): List.splitOnP P xs = [xs] := by
  simp at h
  induction xs with
  | nil => simp
  | cons head tail ih =>
    rw [List.splitOnP_eq_splitOnP2, splitOnP2, ← List.splitOnP_eq_splitOnP2]
    rw [h]
    . simp only [modifyHead, ite_false]
      split
      case h_1 heq => simp only [splitOnP_nonempty] at heq
      case h_2 s hd tl heq =>
        rw [ih] at heq
        simp only [cons.injEq] at heq
        . simp only [heq]
        . intro _ h₂
          simp only [mem_cons, h₂, or_true, h]
    . simp only [mem_cons, true_or]


theorem List.splitOnP_prefix (h: ∀ e ∈ xs, P e = false) (h₂: P d = true): List.splitOnP P (xs ++ [d] ++ tl) = xs :: List.splitOnP P tl  := by
  simp [List.splitOnP_eq_splitOnP2]
  induction xs with
  | nil =>
    conv => left; unfold splitOnP2
    simp only [nil_append, singleton_append, modifyHead, h₂, ite_true, splitOnP_eq_splitOnP2]
  | cons head tail ih =>
    conv => left; unfold splitOnP2
    simp only [cons_append, append_assoc, singleton_append, mem_cons, splitOnP_eq_splitOnP2, modifyHead, true_or,
      h, ite_false]
    split
    case h_1 heq =>
      simp [← List.splitOnP_eq_splitOnP2, splitOnP_nonempty] at heq
    case h_2 heq =>
      rw [ih] at heq
      . congr
        . simp_all only [mem_cons, or_true, implies_true, forall_true_left, forall_eq_or_imp, cons.injEq]
        . simp only [cons.injEq] at heq
          simp only [heq]
      . intro e ein
        simp only [mem_cons, ein, or_true, h]
      

    

theorem List.intercalate_splitOn (s: List Char) (delim: Char): List.intercalate [delim] (List.splitOn delim s) = s := by
  rw [List.splitOn, List.splitOnP_eq_splitOnP2]
  induction s with
  | nil => 
    unfold intercalate splitOnP2
    simp only [join, append_nil]
  | cons head tail tail_ih =>
    unfold intercalate splitOnP2
    if h: head = delim then
      unfold intersperse
      simp [Array.push, h]
      split
      next => simp at *
      next _ _ heq =>
        simp at *
        let ⟨_, h₂⟩ := heq
        have h₃: _  :=  @List.splitOnP_nonempty _ (fun x ↦ x == delim) tail
        conv at h₂ => rw [← List.splitOnP_eq_splitOnP2]
        contradiction
      next xs ys _ _ heq=> 
        simp at *
        let ⟨_, h₂⟩ := heq
        have h₃ : ys = [] := by apply Eq.symm; assumption
        simp [h₃]
        rw [← intercalate, ← h₂]
        simp [tail_ih, h]
    else
      simp [*]
      split
      next heq =>
        have h₂: _  :=  @List.splitOnP_nonempty _ (fun x ↦ x == delim) tail
        conv at h₂ => rw [List.splitOnP_eq_splitOnP2]
        contradiction
      next heq =>
        unfold intersperse
        simp
        split
        next => simp at *
        next heq₂ => 
          simp at *
          let ⟨l, r⟩ := heq₂
          rw [← l]
          rw [r] at heq
          conv at tail_ih =>
            rw [heq]
            unfold intercalate intersperse
            simp
          simp only [cons.injEq, true_and, tail_ih]
        next heq₂ =>
          simp at heq₂
          let ⟨l, r⟩ := heq₂
          rw [← l]
          rw [r] at heq
          rw [heq] at tail_ih
          rw [← tail_ih, intercalate]
          simp

theorem List.intercalateTR.go_accumulates: intercalateTR.go sep x xs (acc ++ tl) = acc.toList ++ intercalateTR.go sep x xs (tl) := by
  induction xs generalizing acc tl x with
  | nil =>
    unfold go
    simp only [Array.toListAppend_eq, Array.append_data, append_assoc, Array.toList_eq, join, append_nil]
  | cons h t ih =>
    unfold go
    rw [ih, ih]
    simp only [Array.toList_eq, Array.appendList_data, Array.append_data, append_assoc]

theorem List.splitOn_intercalate (l: List (List Char)) (delim: Char) (P: l≠ []) (Q: ∀ e ∈ l, delim ∉ e): List.splitOn delim (List.intercalate [delim] l) = l := by
  induction  l with
  | nil =>
    simp only at P
  | cons head tail ih =>
    unfold List.splitOn
    rw [List.intercalate_eq_intercalateTR, intercalateTR]
    split
    case h_1 heq => simp only at heq
    case h_2 elem heq =>
      rw [heq, List.splitOnP_all_false]
      intro c cin
      have h₂: elem ∈ head::tail := by rw [heq ]; apply List.mem_singleton_self
      have h₃ := Q elem h₂
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro contr
      rw [contr] at cin
      contradiction
    case h_3 heq =>
      simp only [cons.injEq] at heq
      have ⟨heq₁,heq₂⟩  := heq
      rw [← heq₁, ← heq₂]
      unfold intercalateTR.go
      cases tail with
      | nil =>
        simp only [Array.toListAppend_eq, Array.data_toArray, nil_append]
        apply splitOnP_all_false
        intro e ein
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro contr
        rw [contr] at ein
        have R:= Q head (List.mem_singleton_self head)
        contradiction
      | cons hd tl =>
        simp only [intercalate_eq_intercalateTR.go, Array.append_data, Array.appendList_data, Array.data_toArray,
        nil_append]
        rw [List.splitOnP_prefix, ← intercalate, cons_inj, ←splitOn, ih]
        . simp only [ne_eq, not_false_iff]
        . intro e ein
          apply Q
          simp_all only [ne_eq, mem_cons, or_true, not_false_iff, implies_true, forall_const, forall_true_left,
  forall_eq_or_imp, and_true]
        . simp only [beq_eq_false_iff_ne, ne_eq]
          intro e ein contr
          apply Q head
          . simp only [mem_cons, true_or]
          . simp only [← contr, ein]
        . simp only [beq_self_eq_true]


def List.splitOnListAux [DecidableEq α] (delim: List α) (l:List α) (acc: Array α) (r: Array (Array α)): (Array (Array α)) :=
  match l with
  | [] => r.push acc
  | head::tail =>
    match h: getRest l delim with
    | none => List.splitOnListAux delim tail (acc.push head) r
    | some rest => 
      have decreasing: List.length rest ≤  1 + List.length l := by simp [h]
      List.splitOnListAux delim rest #[] (r.push acc)
  decreasing_by
    . decreasing_tactic 

def List.splitOnList (delim: List α) (l: List α): List (List α) :=
  if delim <+: l then



  
    

def elf_to_string (e: List Int): List Char :=
  List.intercalate ['\n'] (List.map Int.reprΔ e) ++ ['\n']

def elves_to_string (elves: List (List Int)) : List Char := 
  List.intercalate ['\n'] (List.map elf_to_string elves)


def stringToElvesAux (s:List Char) (int_acc: List Char) (elf_acc:List Int) (elves_acc: List (List Int)): List (List Int) :=
  match s with
  | [] => elves_acc
  | '\n'::('\n'::tail) => stringToElvesAux tail [] [] (elves_acc ++ [elf_acc])
  | '\n'::tail => stringToElvesAux tail [] (elf_acc ++ [String.toIntΔ int_acc]) elves_acc
  | head::tail => stringToElvesAux tail  (int_acc ++ [head]) elf_acc elves_acc
   

def stringToElves (s: List Char) : List (List Int) :=
  stringToElvesAux s [] [] []

#eval List.splitOn '\n' (elves_to_string  [])
    |> List.dropLast
    |> List.splitOn []

#eval stringToElves  ['2', '\n', '\n', '\n', '\n', '4', '\n', '\n', '5', '\n', '3', '6', '\n', '7', '\n']
#eval elves_to_string  [[2],[],[4], [5,36,7]]
#eval List.splitOn '\n' ['2', '\n', '\n', '\n', '\n', '4', '\n', '\n', '5', '\n', '3', '6', '\n', '7', '\n']
#eval stringToElves (elves_to_string [[1,2,3], [], [], []])
theorem elves_roundtrip (elves: List (List Int)): string_to_elves (elves_to_string elves) = elves := by
  unfold string_to_elves elves_to_string elf_to_string
  rw [List.splitOn_intercalate]
  . simp
  . simp
  . simp
  