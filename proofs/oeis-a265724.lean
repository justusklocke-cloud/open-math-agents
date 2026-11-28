import OMAStatements.S_oeis_a265724
import Mathlib

namespace A265724Aux

open OMA.S_oeis_a265724 in
lemma new_on (l c r : Bool) : ruleOut 1 l c r = true ↔ l ≠ true ∧ c ≠ true ∧ r ≠ true := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a265724 in
lemma odd_of_even (m : ℕ) (h : ∀ i, cell 1 m i = true ↔ i = 0) :
    ∀ i, cell 1 (m + 1) i = true ↔ i < -1 ∨ 1 < i := by
  intro i
  rw [cell, new_on]
  simp only [ne_eq, h]
  omega

open OMA.S_oeis_a265724 in
lemma even_of_odd (m : ℕ) (h : ∀ i, cell 1 m i = true ↔ i < -1 ∨ 1 < i) :
    ∀ i, cell 1 (m + 1) i = true ↔ i = 0 := by
  intro i
  rw [cell, new_on]
  simp only [ne_eq, h]
  omega

open OMA.S_oeis_a265724 in
lemma phases (k : ℕ) : (∀ i, cell 1 (2 * k) i = true ↔ i = 0) ∧
    (∀ i, cell 1 (2 * k + 1) i = true ↔ i < -1 ∨ 1 < i) := by
  induction k with
  | zero =>
    have h : ∀ i, cell 1 (2 * 0) i = true ↔ i = 0 := by simp [cell]
    exact ⟨h, odd_of_even _ h⟩
  | succ k ih =>
    have h : ∀ i, cell 1 (2 * (k + 1)) i = true ↔ i = 0 :=
      even_of_odd (2 * k + 1) ih.2
    exact ⟨h, odd_of_even _ h⟩

open OMA.S_oeis_a265724 in
lemma on_even (k : ℕ) : ((onCount 1 (2 * k) : ℕ) : ℤ) = 1 := by
  have h := (phases k).1
  generalize 2 * k = n at h ⊢
  unfold onCount
  have val : ∀ j : ℕ, (if cell 1 n ((j : ℤ) - n) = true then 1 else 0) =
      (if j = n then 1 else 0) := by
    intro j
    simp only [h]
    split_ifs <;> omega
  have hn : n < 2 * n + 1 := by omega
  simp only [val]
  simp [hn]

open OMA.S_oeis_a265724 in
lemma on_odd (k : ℕ) : ((onCount 1 (2 * k + 1) : ℕ) : ℤ) = 4 * (k : ℤ) := by
  have h := (phases k).2
  have hk : 1 ≤ 2 * k + 1 := by omega
  have e : (4 * (k : ℤ)) = 2 * ((2 * k + 1 : ℕ) : ℤ) + 1 - 3 := by push_cast; ring
  rw [e]
  generalize 2 * k + 1 = n at h hk ⊢
  unfold onCount
  have val : ∀ j : ℕ, (if cell 1 n ((j : ℤ) - n) = true then (1 : ℤ) else 0) =
      1 - (if j = n - 1 then (1 : ℤ) else 0) - (if j = n then (1 : ℤ) else 0)
        - (if j = n + 1 then (1 : ℤ) else 0) := by
    intro j
    simp only [h]
    split_ifs <;> omega
  have h1 : n - 1 < 2 * n + 1 := by omega
  have h2 : n < 2 * n + 1 := by omega
  have h3 : n + 1 < 2 * n + 1 := by omega
  push_cast
  simp only [val]
  simp [Finset.sum_sub_distrib, h1, h2, h3]
  ring

open OMA.S_oeis_a265724 in
lemma a_succ (n : ℕ) : a (n + 1) = a n + ((2 * ((n + 1 : ℕ) : ℤ) + 1) - onCount 1 (n + 1)) := by
  unfold a
  rw [Finset.sum_range_succ]

open OMA.S_oeis_a265724 in
lemma a_zero : a 0 = 0 := by
  unfold a
  have h := on_even 0
  simp only [Nat.mul_zero] at h
  simp [h]

open OMA.S_oeis_a265724 in
lemma closed (k : ℕ) : a (2 * k) = 2 * (k : ℤ) ^ 2 + 5 * k ∧
    a (2 * k + 1) = 2 * (k : ℤ) ^ 2 + 5 * k + 3 := by
  induction k with
  | zero =>
    refine ⟨by simpa using a_zero, ?_⟩
    have h := a_succ 0
    rw [a_zero, show 0 + 1 = 2 * 0 + 1 from rfl, on_odd 0] at h
    rw [h] <;> norm_num
  | succ k ih =>
    have h1 : a (2 * (k + 1)) = 2 * ((k + 1 : ℕ) : ℤ) ^ 2 + 5 * ((k + 1 : ℕ) : ℤ) := by
      have h := a_succ (2 * k + 1)
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring] at h
      rw [h, ih.2, on_even]
      push_cast
      ring
    refine ⟨h1, ?_⟩
    have h := a_succ (2 * (k + 1))
    rw [h, h1, on_odd]
    push_cast
    ring

open OMA.S_oeis_a265724 in
lemma a_cl (n : ℕ) : (a n : ℚ) =
    1 / 2 * ((n : ℚ) ^ 2 + (-1 : ℚ) ^ n * (n : ℚ) + 4 * (n : ℚ) - (-1 : ℚ) ^ n + 1) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have e : (-1 : ℚ) ^ (2 * k) = 1 := by rw [pow_mul] <;> norm_num
    rw [(closed k).1, e]
    push_cast
    ring
  · have e : (-1 : ℚ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul] <;> norm_num
    rw [(closed k).2, e]
    push_cast
    ring

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A265724Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a265724 A265724Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a265724.main := by
  refine ⟨a_cl, ?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ := hn
    rw [← two_mul, (closed k).1]
    push_cast
    ring
  · intro n hn
    obtain ⟨k, rfl⟩ := hn
    rw [(closed k).2]
    push_cast
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
      show m + 5 - 5 = m by omega]
    rw [a_cl (m + 5), a_cl (m + 4), a_cl (m + 3), a_cl (m + 2), a_cl (m + 1), a_cl m]
    push_cast
    ring
  · have hD : ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-1) * PowerSeries.X ^ 1 +
        PowerSeries.C (-2) * PowerSeries.X ^ 2 + PowerSeries.C 2 * PowerSeries.X ^ 3 +
        PowerSeries.C 1 * PowerSeries.X ^ 4 + PowerSeries.C (-1) * PowerSeries.X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (PowerSeries.X * (3 + 4 * PowerSeries.X - 3 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C 3 * PowerSeries.X ^ 1 + PowerSeries.C 4 * PowerSeries.X ^ 2 +
        PowerSeries.C (-3) * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    have e0 := a_cl 0
    have e1 := a_cl 1
    have e2 := a_cl 2
    have e3 := a_cl 3
    have e4 := a_cl 4
    norm_num at e0 e1 e2 e3 e4
    rcases n with _ | _ | _ | _ | _ | n
    · simp [e0]
    · simp [e0, e1] <;> norm_num
    · simp [e0, e1, e2] <;> norm_num
    · simp [e0, e1, e2, e3] <;> norm_num
    · simp [e0, e1, e2, e3, e4] <;> norm_num
    · have f5 := a_cl (n + 5)
      have f4 := a_cl (n + 4)
      have f3 := a_cl (n + 3)
      have f2 := a_cl (n + 2)
      have f1 := a_cl (n + 1)
      have f0 := a_cl n
      simp [f5, f4, f3, f2, f1, f0]
      ring
