import OMAStatements.S_oeis_a273675
import Mathlib

namespace A273675Aux

open OMA.S_oeis_a273675 in
lemma step_gen (code t : ℕ) (f g : ℤ → ℤ → Bool)
    (hf : ∀ i j, cell code t i j = f i j)
    (h : ∀ (i j : ℤ) (c n1 n2 n3 n4 : Bool), f i j = c → f (i + 1) j = n1 → f (i - 1) j = n2 →
      f i (j + 1) = n3 → f i (j - 1) = n4 →
      g i j = code.testBit (c.toNat + 2 * (n1.toNat + n2.toNat + n3.toNat + n4.toNat))) :
    ∀ i j, cell code (t + 1) i j = g i j := by
  intro i j
  show code.testBit ((cell code t i j).toNat + 2 * ((cell code t (i + 1) j).toNat +
      (cell code t (i - 1) j).toNat + (cell code t i (j + 1)).toNat +
      (cell code t i (j - 1)).toNat)) = g i j
  rw [hf, hf, hf, hf, hf]
  exact (h i j _ _ _ _ _ rfl rfl rfl rfl rfl).symm

/-- the diamond of radius `t` restricted to the cells with `i + j + t` even -/
def dmb (t : ℕ) (i j : ℤ) : Bool :=
  decide (i + j ≤ t ∧ -(t : ℤ) ≤ i + j ∧ i - j ≤ t ∧ -(t : ℤ) ≤ i - j ∧ (i + j + t) % 2 = 0)

def p0 (i j : ℤ) : Bool := decide (i = 0 ∧ j = 0)
def p1 (i j : ℤ) : Bool := decide (¬(i + j ≤ 1 ∧ -1 ≤ i + j ∧ i - j ≤ 1 ∧ -1 ≤ i - j))
def p2 (i j : ℤ) : Bool :=
  decide (¬(i + j ≤ 2 ∧ -2 ≤ i + j ∧ i - j ≤ 2 ∧ -2 ≤ i - j ∧ (i + j) % 2 = 0 ∧ ¬(i = 0 ∧ j = 0)))
def pd (t : ℕ) (i j : ℤ) : Bool := !dmb t i j

lemma tr_0_1 : ∀ (i j : ℤ) (c n1 n2 n3 n4 : Bool), p0 i j = c → p0 (i + 1) j = n1 →
    p0 (i - 1) j = n2 → p0 i (j + 1) = n3 → p0 i (j - 1) = n4 →
    p1 i j = Nat.testBit 833 (c.toNat + 2 * (n1.toNat + n2.toNat + n3.toNat + n4.toNat)) := by
  intro i j c n1 n2 n3 n4 h0 h1 h2 h3 h4
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;>
    simp only [p0, p1, decide_eq_true_eq, decide_eq_false_iff_not, not_not, Bool.toNat_true,
      Bool.toNat_false, Nat.testBit_eq_decide_div_mod_eq] at h0 h1 h2 h3 h4 ⊢ <;>
    norm_num <;> omega

lemma tr_1_2 : ∀ (i j : ℤ) (c n1 n2 n3 n4 : Bool), p1 i j = c → p1 (i + 1) j = n1 →
    p1 (i - 1) j = n2 → p1 i (j + 1) = n3 → p1 i (j - 1) = n4 →
    p2 i j = Nat.testBit 833 (c.toNat + 2 * (n1.toNat + n2.toNat + n3.toNat + n4.toNat)) := by
  intro i j c n1 n2 n3 n4 h0 h1 h2 h3 h4
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;>
    simp only [p1, p2, decide_eq_true_eq, decide_eq_false_iff_not, not_not, Bool.toNat_true,
      Bool.toNat_false, Nat.testBit_eq_decide_div_mod_eq] at h0 h1 h2 h3 h4 ⊢ <;>
    norm_num <;> omega

lemma tr_2_3 : ∀ (i j : ℤ) (c n1 n2 n3 n4 : Bool), p2 i j = c → p2 (i + 1) j = n1 →
    p2 (i - 1) j = n2 → p2 i (j + 1) = n3 → p2 i (j - 1) = n4 →
    pd 3 i j = Nat.testBit 833 (c.toNat + 2 * (n1.toNat + n2.toNat + n3.toNat + n4.toNat)) := by
  intro i j c n1 n2 n3 n4 h0 h1 h2 h3 h4
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;>
    simp only [p2, pd, dmb, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
      decide_eq_true_eq, decide_eq_false_iff_not, not_not, Bool.toNat_true,
      Bool.toNat_false, Nat.testBit_eq_decide_div_mod_eq] at h0 h1 h2 h3 h4 ⊢ <;>
    norm_num <;> omega

set_option maxHeartbeats 4000000 in
lemma tr_d (t : ℕ) (ht : 3 ≤ t) : ∀ (i j : ℤ) (c n1 n2 n3 n4 : Bool), pd t i j = c →
    pd t (i + 1) j = n1 → pd t (i - 1) j = n2 → pd t i (j + 1) = n3 → pd t i (j - 1) = n4 →
    pd (t + 1) i j =
      Nat.testBit 833 (c.toNat + 2 * (n1.toNat + n2.toNat + n3.toNat + n4.toNat)) := by
  intro i j c n1 n2 n3 n4 h0 h1 h2 h3 h4
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;>
    simp only [pd, dmb, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
      decide_eq_true_eq, decide_eq_false_iff_not, not_not, Bool.toNat_true,
      Bool.toNat_false, Nat.testBit_eq_decide_div_mod_eq] at h0 h1 h2 h3 h4 ⊢ <;>
    norm_num <;> push_cast <;> omega

open OMA.S_oeis_a273675 in
lemma c0 : ∀ i j, cell 833 0 i j = p0 i j := by
  intro i j
  rfl

open OMA.S_oeis_a273675 in
lemma c1 : ∀ i j, cell 833 1 i j = p1 i j := step_gen 833 0 p0 p1 c0 tr_0_1

open OMA.S_oeis_a273675 in
lemma c2 : ∀ i j, cell 833 2 i j = p2 i j := step_gen 833 1 p1 p2 c1 tr_1_2

open OMA.S_oeis_a273675 in
lemma cN (t : ℕ) (ht : 3 ≤ t) : ∀ i j, cell 833 t i j = pd t i j := by
  induction t, ht using Nat.le_induction with
  | base => exact step_gen 833 2 p2 (pd 3) c2 tr_2_3
  | succ k hk ih => exact step_gen 833 k (pd k) (pd (k + 1)) ih (tr_d k hk)

lemma cnt_par (lo m N : ℕ) :
    ∑ j ∈ Finset.range N, (if lo ≤ j ∧ j ≤ lo + 2 * m ∧ (j + lo) % 2 = 0 then 1 else 0) =
      (min N (lo + 2 * m + 1) + 1 - lo) / 2 := by
  induction N with
  | zero =>
    simp
    omega
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

lemma dia_row (t i : ℕ) (hi : i ≤ 2 * t) :
    ∑ j ∈ Finset.range (2 * t + 1),
      (if dmb t ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0) = min i (2 * t - i) + 1 := by
  have h := cnt_par (t - min i (2 * t - i)) (min i (2 * t - i)) (2 * t + 1)
  rw [show (min (2 * t + 1) (t - min i (2 * t - i) + 2 * min i (2 * t - i) + 1) + 1 -
    (t - min i (2 * t - i))) / 2 = min i (2 * t - i) + 1 by omega] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  simp only [dmb, decide_eq_true_eq]
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

lemma tri (t : ℕ) : ∑ i ∈ Finset.range (2 * t + 1), (min i (2 * t - i) + 1) = (t + 1) ^ 2 := by
  induction t with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ']
    have h : ∀ i ∈ Finset.range (2 * k + 1),
        min (i + 1) (2 * (k + 1) - (i + 1)) + 1 = (min i (2 * k - i) + 1) + 1 := by
      intro i hi
      have := Finset.mem_range.mp hi
      omega
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ih]
    have e1 : min 0 (2 * (k + 1) - 0) + 1 = 1 := by omega
    have e2 : min (2 * k + 1 + 1) (2 * (k + 1) - (2 * k + 1 + 1)) + 1 = 1 := by omega
    rw [e1, e2]
    simp
    ring

lemma dia_total (t : ℕ) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if dmb t ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0) = (t + 1) ^ 2 := by
  rw [Finset.sum_congr rfl (fun i hi => dia_row t i (by have := Finset.mem_range.mp hi; omega))]
  exact tri t

lemma compl2 (p : ℤ → ℤ → Bool) (t : ℕ) :
    (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0)) +
      (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 0 else 1)) =
      (2 * t + 1) * (2 * t + 1) := by
  rw [← Finset.sum_add_distrib]
  have h : ∀ i ∈ Finset.range (2 * t + 1),
      (∑ j ∈ Finset.range (2 * t + 1), (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0)) +
      (∑ j ∈ Finset.range (2 * t + 1), (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 0 else 1))
      = 2 * t + 1 := by
    intro i _
    rw [← Finset.sum_add_distrib]
    have h2 : ∀ j ∈ Finset.range (2 * t + 1),
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0) +
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 0 else 1) = 1 := by
      intro j _
      split_ifs <;> rfl
    rw [Finset.sum_congr rfl h2]
    simp
  rw [Finset.sum_congr rfl h]
  simp

open OMA.S_oeis_a273675 in
lemma on0 : onCount 833 0 = 1 := by
  unfold onCount
  simp only [c0]
  decide

open OMA.S_oeis_a273675 in
lemma on1 : onCount 833 1 = 4 := by
  unfold onCount
  simp only [c1]
  decide

open OMA.S_oeis_a273675 in
lemma on2 : onCount 833 2 = 17 := by
  unfold onCount
  simp only [c2]
  decide

open OMA.S_oeis_a273675 in
lemma onN (t : ℕ) (ht : 3 ≤ t) :
    (onCount 833 t : ℤ) = (2 * (t : ℤ) + 1) ^ 2 - ((t : ℤ) + 1) ^ 2 := by
  unfold onCount
  simp only [cN t ht, pd]
  have h1 := compl2 (dmb t) t
  rw [dia_total] at h1
  have h4 : ∀ b : Bool, (if (!b) = true then (1 : ℕ) else 0) = (if b = true then 0 else 1) := by
    intro b
    cases b <;> rfl
  simp only [h4]
  have h3 := congrArg (fun z : ℕ => (z : ℤ)) h1
  push_cast at h3 ⊢
  linarith

open OMA.S_oeis_a273675 in
lemma onQ (t : ℕ) (ht : 3 ≤ t) :
    (onCount 833 t : ℚ) = (2 * (t : ℚ) + 1) ^ 2 - ((t : ℚ) + 1) ^ 2 := by
  have h := onN t ht
  have h2 : ((onCount 833 t : ℤ) : ℚ) = (2 * (t : ℚ) + 1) ^ 2 - ((t : ℚ) + 1) ^ 2 := by
    rw [h]; push_cast; ring
  exact_mod_cast h2

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

open OMA.S_oeis_a273675 in
lemma oq0 : (onCount 833 0 : ℚ) = 1 := by
  rw [on0]; norm_num

open OMA.S_oeis_a273675 in
lemma oq1 : (onCount 833 1 : ℚ) = 4 := by
  rw [on1]; norm_num

open OMA.S_oeis_a273675 in
lemma oq2 : (onCount 833 2 : ℚ) = 17 := by
  rw [on2]; norm_num

open OMA.S_oeis_a273675 in
lemma oq3 : (onCount 833 3 : ℚ) = 33 := by
  rw [onQ 3 (by norm_num)]; norm_num

open OMA.S_oeis_a273675 in
lemma oq4 : (onCount 833 4 : ℚ) = 56 := by
  rw [onQ 4 (by norm_num)]; norm_num

open OMA.S_oeis_a273675 in
lemma oq5 : (onCount 833 5 : ℚ) = 85 := by
  rw [onQ 5 (by norm_num)]; norm_num

open OMA.S_oeis_a273675 in
lemma oq6 : (onCount 833 6 : ℚ) = 120 := by
  rw [onQ 6 (by norm_num)]; norm_num

open OMA.S_oeis_a273675 in
lemma oq7 : (onCount 833 7 : ℚ) = 161 := by
  rw [onQ 7 (by norm_num)]; norm_num

open OMA.S_oeis_a273675 in
lemma oq8 : (onCount 833 8 : ℚ) = 208 := by
  rw [onQ 8 (by norm_num)]; norm_num

open OMA.S_oeis_a273675 in
lemma e0 : (a 0 : ℚ) = 1 := by
  unfold a; push_cast; rw [oq0]

open OMA.S_oeis_a273675 in
lemma e1 : (a 1 : ℚ) = 4 := by
  unfold a; push_cast; rw [oq1]

open OMA.S_oeis_a273675 in
lemma e2 : (a 2 : ℚ) = 17 := by
  unfold a; push_cast; rw [oq2]

open OMA.S_oeis_a273675 in
lemma e3 : (a 3 : ℚ) = 33 := by
  unfold a; push_cast; rw [oq3]

open OMA.S_oeis_a273675 in
lemma e4 : (a 4 : ℚ) = 56 := by
  unfold a; push_cast; rw [oq4]

open OMA.S_oeis_a273675 in
lemma e5 : (a 5 : ℚ) = 85 := by
  unfold a; push_cast; rw [oq5]

open OMA.S_oeis_a273675 in
lemma e6 : (a 6 : ℚ) = 120 := by
  unfold a; push_cast; rw [oq6]

open OMA.S_oeis_a273675 in
lemma aQ (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = (2 * (n : ℚ) + 1) ^ 2 - ((n : ℚ) + 1) ^ 2 := by
  unfold a; push_cast; rw [onQ n (by omega)]

end A273675Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a273675 A273675Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a273675.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [aQ n (by omega)]
    first | done | ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega]
    rw [aQ (m + 6) (by omega), aQ (m + 5) (by omega), aQ (m + 4) (by omega), aQ (m + 3) (by omega)]
    push_cast
    ring
  · have hD : ((1 - X) ^ 3 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-3) * PowerSeries.X ^ 1 + PowerSeries.C 3 * PowerSeries.X ^ 2 + PowerSeries.C (-1) * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + X + 8 * X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4 - X ^ 5 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 1 * PowerSeries.X ^ 1 + PowerSeries.C 8 * PowerSeries.X ^ 2 + PowerSeries.C (-7) * PowerSeries.X ^ 3 + PowerSeries.C 4 * PowerSeries.X ^ 4 + PowerSeries.C (-1) * PowerSeries.X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e0, e1]
    · norm_num [e0, e1, e2]
    · norm_num [e0, e1, e2, e3]
    · norm_num [e1, e2, e3, e4]
    · norm_num [e2, e3, e4, e5]
    · have f3 := aQ (n + 3) (by omega)
      have f4 := aQ (n + 4) (by omega)
      have f5 := aQ (n + 5) (by omega)
      have f6 := aQ (n + 6) (by omega)
      simp [show n + 6 - 1 = n + 5 by omega, show n + 6 - 2 = n + 4 by omega, show n + 6 - 3 = n + 3 by omega, f3, f4, f5, f6]
      ring
