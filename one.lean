import Lean
import Mathlib.data.list.basic
import Mathlib.Tactic.Find
import Mathlib.Tactic.LibrarySearch
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

theorem List.getD_singleton {n : Nat} (elem: α): List.getD [elem] n elem = elem := by
  unfold getD get? Option.getD
  simp only [cons.injEq, and_imp, forall_apply_eq_imp_iff', forall_eq']
  cases n
  . simp only
  . simp only [get?]

theorem Nat.toDigitsCore_shift' (b:ℕ) (n:ℕ) (P: b>1): ∀i:ℕ, (Nat.toDigits b n).reverse.getD (i+1) '0' = (Nat.toDigits b (n/b)).reverse.getD i '0':= by
  intro i
  conv =>
    left
    unfold toDigits toDigitsCore
  simp
  split
  . next heq =>
    conv => left; unfold List.getD
    simp
    rw [heq]
    unfold toDigits toDigitsCore digitChar
    simp
    
  . next heq =>
    rw [Nat.todigitsCore_accumulates_suffix]
    rw [List.getD, List.getD]
    congr 1
    simp
    rw [Nat.toDigitsCore_fuel_irrelevant, ← Nat.toDigits]
    . simp
      have h: n ≠ 0 := by 
        simp only [ne_eq]
        intro h
        rw [h] at heq
        simp only [Nat.zero_div] at heq
      apply Nat.div_lt_self
      . simp [h, Nat.ne_zero_gt_zero]
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



theorem Nat.toDigits_eq_digit_rev (b: ℕ) (n:ℕ) (P: b > 1): 
 ∀ i:ℕ, (Nat.toDigits b n).reverse.getD i '0' = Nat.digitChar (Nat.digit b n i) := by
  intro i
  rw [Nat.toDigitsCore_shift_full]
  . unfold toDigits toDigitsCore digit
    simp
    split
    . next heq =>
      simp [List.getD]
    . next heq =>
      rw [Nat.todigitsCore_accumulates_suffix]
      simp [List.getD]
  . exact P

#find _ / _ = 0 -> _
theorem Nat.toDigitsCore_length_eq_log  (b fuel n: ℕ ) (P: b>1) (R: fuel>n): List.length (Nat.toDigitsCore b fuel n accum) = Nat.log b n + 1 + List.length accum:= by
  have heq: accum = [] ++ accum := by simp
  rw [heq, Nat.toDigitsCore_accumulates]
  simp
  induction n using Nat.strong_induction_on generalizing fuel accum
  case h n ih =>
    unfold toDigitsCore
    split
    . next i _ _ _=> 
      exfalso
      apply Nat.not_lt_of_le (Nat.zero_le i)
      apply Q
    . next =>
      simp; split
      . next  i _ _ _ _ h₂=>
        simp
        left
        have  h: b > 0 :=by library_search
        apply Nat.div_lt_one_iff h
theorem Nat.toDigits_eq_digit (b n:ℕ) (P: b>1):
 ∀ i:ℕ, i < List.length (Nat.toDigits b n) →  List.getD (Nat.toDigits b n) i '0' = Nat.digitChar (Nat.digit b n (List.length (Nat.toDigits b n) - 1 - i)) := by
  intro i h
  rw [← Nat.toDigits_eq_digit_rev b n P (List.length (Nat.toDigits b n) - 1 - i)]
  rw [ List.getD, List.getD, List.get?_reverse]
  congr
  . have h₂: List.length (toDigits b n) - 1 ≥ (List.length (toDigits b n) - 1 - i) := by simp
    have h₃: List.length (toDigits b n) ≥ 1 := by calc 
      List.length (toDigits b n) > i := h
      _ ≥ 0 := by simp
    have h₄: i ≤ List.length (toDigits b n) - 1 := by apply Nat.le_pred_of_lt; exact h
    zify [h₂, h₃, h₄]
    apply Int.eq_of_sub_eq_zero
    ring_nf
  . rw [Nat.sub_sub]
    apply Nat.sub_lt_self
    . simp
    . rw [Nat.add_comm]
      apply Nat.lt_iff_add_one_le.1 h


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
  | nil => simp at h
  | cons => simp

@[simp]
theorem List.drop_one_eq_tail (l:List α): l.drop 1 = l.tail := by
  induction l <;> simp

@[simp]
theorem List.drop_eq_cons (i) (l: List α) (h: i < l.length): l[i] :: l.drop (i+1) = l.drop i := by
  induction l generalizing i with
  | nil => simp at h
  | cons head tail ih =>
    conv => right; unfold drop
    split
    . next => simp
    . next heq=> 
      simp at heq
    . next z x n hd tl heq=>
      simp at heq
      have ⟨ _,heq₂⟩ := heq
      rw [ ←heq₂]
      apply ih


lemma reverse_index_valid (n) (k) (P:n<k): k-1-n < k := by 
  rw [Nat.sub_sub]
  apply Nat.sub_lt_self
  . simp
  . apply Nat.le_of_lt_succ
    rw [Nat.succ_eq_add_one, Nat.add_comm]
    simp [P]

@[simp]
theorem List.drop_eq_cons_drop (n) (l:List α) (h:n < length l):
  (List.get l ⟨n, h⟩ ) :: (List.drop (n+1) l) = List.drop n l := by
  induction l generalizing n
  . case nil => simp at h
  . case cons head tail ih =>
    cases n with
    | zero => simp
    | succ n => simp [ih]

@[simp]
theorem List.lastN_eq_cons_lastN (n) (l:List α) (P:n < l.length): 
get l ⟨ l.length - 1 - n, reverse_index_valid n l.length P⟩::(List.lastN n l) = List.lastN (n+1) l := by
  unfold lastN
  have h:  length l - (n + 1) < length l := by
    apply Nat.sub_lt_self
    . simp
    . simp [← Nat.succ_eq_add_one, Nat.succ_le_of_lt, P]

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
    . simp [Nat.le_of_lt, P]


@[simp]
theorem List.take_cons (n) (head:α) (tail:List α): List.take (n+1) (head::tail) = head::(List.take n tail) := by
  simp

@[simp]
theorem List.drop_cons (n) (head:α) (tail:List α): List.drop (n+1) (head::tail) = List.drop n tail := by
  simp

@[simp]
theorem List.take_append (n) (l₁ l₂:List α) (P:n ≤ l₁.length): List.take n (l₁++l₂) = List.take n l₁ := by
  induction l₁ generalizing n with
  | nil =>
    simp_all
  | cons head tail ih =>
    cases n with
    | zero =>
      simp
    | succ n =>
      simp
      rw [ih]
      simp at P
      rw [← Nat.succ_le_succ_iff]
      apply P
      
theorem List.lastN_eq_reverse_take (n:ℕ) (l: List α): List.lastN n l = (List.take n l.reverse).reverse := by
  unfold List.lastN
  induction l generalizing n with
  | nil => simp
  | cons head tail ih =>
    simp
    cases h: decide (n ≤ length tail) with
    | false => 
      simp at h
      rw [Nat.succ_eq_add_one, Nat.add_comm]
      rw [List.take_length_le, List.reverse_append, List.reverse_reverse]
      simp
      have heq : 1 + length tail - n = 0 := by simp; rw [Nat.add_comm]; apply Nat.le_of_lt_succ; rw [Nat.succ_eq_add_one]; simp [h]
      rw [heq]
      simp [h]
      rw [List.length_append, List.length_reverse]
      simp
      exact h
    | true =>
      simp at h
      rw [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_sub_assoc, Nat.add_comm, List.drop_cons, ih]
      congr 1
      rw [List.take_append]
      . simp; apply h
      . apply h

@[simp]
theorem Nat.digitChar_sub_zero_eq_self (n:ℕ) (P: n<10): Char.toNat (Nat.digitChar n) - Char.toNat '0' = n := by
  revert n
  decide

theorem Nat.toDigits_modulo (b n p i:ℕ) (P: i<p) (Q: b>1): List.getD (Nat.toDigits b (n % b^p)) (List.length (Nat.toDigits b (n % b^p))-1-i) '0' = List.getD (Nat.toDigits b n) (List.length (Nat.toDigits b n)-1-i) '0' := by
  repeat rw [Nat.toDigits_eq_digit]
  congr 1
  unfold digit
  cases h:decide (i< List.length (Nat.toDigits b (n % b^p))) with
  | true => 
    simp at h
    cases h₂:decide (i< List.length (Nat.toDigits b n)) with
    | true =>
      simp at h₂
      repeat rw [Nat.sub_sub_self]
      . have h₃: b^p = b^i * b^(p-i) := by
          rw [← pow_add b, Nat.add_comm, Nat.sub_add_cancel]
          exact Nat.le_of_lt P
        simp [ h₃, Nat.mod_mul_right_div_self]
        rw [Nat.mod_mod_of_dvd]
        apply dvd_pow_self
        apply Nat.sub_ne_zero_of_lt P

      . apply Nat.le_pred_of_lt h₂
      . apply Nat.le_pred_of_lt h
    | false => 
      simp at h₂
      simp [h₂]


    . exact Q
    . exact h
    . exact Q

  | false => simp at h


    
theorem String.toNatΔ_inv_NattoDigits_tail (b:ℕ) (n:ℕ) (i:ℕ) (P: b <= 10) (Q: b > 1): String.toNatΔ (List.lastN i (Nat.toDigits b n)) = String.toNatΔ (Nat.to_digits_core_lens_eq b (n % b^i)) := by
  induction i with
  | zero =>
    simp [Nat.mod_one, Nat.toDigits, Nat.toDigitsCore]
  | succ i ih =>
    rw [← List.lastN_eq_cons_lastN]
    conv => left; unfold toNatΔ toNatAux
    simp
    rw [String.toNatAux_accumulates, ← toNatΔ, ih,
     ← Option.getD_some (a:= List.get _ _) (b:=Char.ofNat 48),
     ← List.get?_eq_get,
     ← List.getD_eq_get?,
     Nat.toDigits_eq_digit,
     Nat.digitChar_sub_zero_eq_self]
    cases h: decide (i < (Nat.toDigits b n).length) with
    | true => 
      simp at h
      have heq:  List.length (Nat.toDigits b n) - 1 - (List.length (Nat.toDigits b n) - 1 - i) = i := 
        Nat.sub_sub_self (Nat.le_sub_of_add_le h)
      rw [heq, List.lastN_length, Nat.min_eq_left (Nat.le_of_lt h)]

    | false => 
      simp at h
      have h₂: List.length (Nat.toDigits b n) - 1 ≤ i := by calc
        List.length (Nat.toDigits b n) - 1 ≤ List.length (Nat.toDigits b n) := by simp only [tsub_le_iff_right, ge_iff_le, le_add_iff_nonneg_right]
        _ ≤ i := h
      simp [h, Nat.sub_eq_zero_of_le h₂]

    
theorem Nat.toDigits_single_digit (b:ℕ) (n:ℕ) (P: n<b): Nat.toDigits b n = [Nat.digitChar n] := by
  unfold toDigits toDigitsCore
  simp
  split
  . next => 
    have h:n % b = n := by exact mod_eq_of_lt P
    simp only [h]
  . next =>
    unfold toDigitsCore
    simp
    split
    . simp
    . split
      . next h _=> exfalso; apply h; exact div_eq_of_lt P
      . next h _=> exfalso; apply h; exact div_eq_of_lt P

@[simp]
theorem Nat.pow_one (n:ℕ): n^1 =n := by 
  simp [Nat.pow_succ, Nat.pow_zero]

theorem String.toNatΔ_inv_NattoDigits (n:ℕ) : String.toNatΔ (Nat.toDigits 10 n) = n := by
    rw [List.lastN]

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

theorem List.splitOn_intercalate (s: List Char) (delim: Char): List.intercalate [delim] (List.splitOn delim s) = s := by
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
  
    

def elf_to_string: List Int -> List Char 
| [] => []
| (h :: []) => (h.toString).data
| (h :: tail) => String.append (String.append (toString h) " ") (elf_to_string tail) 

def elves_to_string (elves: List (List Int)) : String := 
  List.map (λ e => (elf_to_string e) ++ "\n") elves
  |> List.foldl String.append ""


def string_to_elves (s: String) : List (List Int)
  :=
  String.split s (λ c => c = '¬') |>
   List.map (λ st => String.split st (λ c => c = ' ') |> List.map String.toInt!)

lemma String.split_empty (c): String.split "" c = [""] := by
  rw [String.split]; 

theorem elves_roundtrip (elves: List (List Int)): string_to_elves (elves_to_string elves) = elves := by
  induction elves with
  | nil => 
    rw [string_to_elves, elves_to_string]
    simp


