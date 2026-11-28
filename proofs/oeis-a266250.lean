import OMAStatements.S_oeis_a266250
import Mathlib

namespace A266250Aux

open OMA.S_oeis_a266250 in
lemma rule_iff (l c r : Bool) : ruleOut 9 l c r = true ↔
    ((¬ l = true ∧ ¬ c = true ∧ ¬ r = true) ∨ (¬ l = true ∧ c = true ∧ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a266250 in
lemma s0 (i : ℤ) : cell 9 0 i = true ↔ i = 0 := by
  simp [cell]

open OMA.S_oeis_a266250 in
lemma s1 (i : ℤ) : cell 9 1 i = true ↔ ¬(i = -1 ∨ i = 0 ∨ i = 1) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cell, rule_iff]
  simp only [s0]
  omega

open OMA.S_oeis_a266250 in
lemma s2 (i : ℤ) : cell 9 2 i = true ↔ i = 0 ∨ i = 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, cell, rule_iff]
  simp only [s1]
  omega

open OMA.S_oeis_a266250 in
lemma s3 (i : ℤ) : cell 9 3 i = true ↔ ¬(i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, cell, rule_iff]
  simp only [s2]
  omega

open OMA.S_oeis_a266250 in
lemma s4 (i : ℤ) : cell 9 4 i = true ↔ i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 4 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, cell, rule_iff]
  simp only [s3]
  omega

open OMA.S_oeis_a266250 in
lemma state (t : ℕ) (ht : 4 ≤ t) : ∀ i : ℤ, cell 9 t i = true ↔
    ((t % 2 = 0 ∧ (i = (t : ℤ) - 4 ∨ i = (t : ℤ) - 3 ∨ i = (t : ℤ) - 2 ∨ i = t)) ∨
     (t % 2 = 1 ∧ ¬(i = (t : ℤ) - 6 ∨ i = (t : ℤ) - 4 ∨ i = (t : ℤ) - 3 ∨ i = (t : ℤ) - 2 ∨
        i = (t : ℤ) - 1 ∨ i = t))) := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [s4]
    omega
  | succ t ht ih =>
    intro i
    rw [cell, rule_iff]
    simp only [ih]
    push_cast
    omega

open OMA.S_oeis_a266250 in
lemma on_even (t : ℕ) (ht : 4 ≤ t) (he : t % 2 = 0) : ((onCount 9 t : ℕ) : ℤ) = 4 := by
  have h := state t ht
  unfold onCount
  push_cast
  have val : ∀ j : ℕ, (if cell 9 t ((j : ℤ) - t) = true then (1 : ℤ) else 0) =
      (if j = 2 * t - 4 then (1 : ℤ) else 0) + (if j = 2 * t - 3 then (1 : ℤ) else 0) +
      (if j = 2 * t - 2 then (1 : ℤ) else 0) + (if j = 2 * t then (1 : ℤ) else 0) := by
    intro j
    simp only [h]
    split_ifs <;> omega
  have h1 : 2 * t - 4 < 2 * t + 1 := by omega
  have h2 : 2 * t - 3 < 2 * t + 1 := by omega
  have h3 : 2 * t - 2 < 2 * t + 1 := by omega
  simp only [val, Finset.sum_add_distrib]
  simp [h1, h2, h3]

open OMA.S_oeis_a266250 in
lemma on_odd (t : ℕ) (ht : 5 ≤ t) (ho : t % 2 = 1) :
    ((onCount 9 t : ℕ) : ℤ) = 2 * (t : ℤ) - 5 := by
  have h := state t (by omega)
  unfold onCount
  push_cast
  have val : ∀ j : ℕ, (if cell 9 t ((j : ℤ) - t) = true then (1 : ℤ) else 0) =
      1 - (if j = 2 * t - 6 then (1 : ℤ) else 0) - (if j = 2 * t - 4 then (1 : ℤ) else 0) -
      (if j = 2 * t - 3 then (1 : ℤ) else 0) - (if j = 2 * t - 2 then (1 : ℤ) else 0) -
      (if j = 2 * t - 1 then (1 : ℤ) else 0) - (if j = 2 * t then (1 : ℤ) else 0) := by
    intro j
    simp only [h]
    split_ifs <;> omega
  have h0 : 2 * t - 6 < 2 * t + 1 := by omega
  have h1 : 2 * t - 4 < 2 * t + 1 := by omega
  have h2 : 2 * t - 3 < 2 * t + 1 := by omega
  have h3 : 2 * t - 2 < 2 * t + 1 := by omega
  have h4 : 2 * t - 1 < 2 * t + 1 := by omega
  simp only [val, Finset.sum_sub_distrib]
  simp [h0, h1, h2, h3, h4]
  ring

open OMA.S_oeis_a266250 in
lemma on_big (t : ℕ) (ht : 4 ≤ t) : ((onCount 9 t : ℕ) : ℚ) =
    (2 * (t : ℚ) - 1) / 2 + (-1 : ℚ) ^ t * (9 - 2 * (t : ℚ)) / 2 := by
  rcases Nat.even_or_odd t with he | ho
  · have h := on_even t ht (Nat.even_iff.mp he)
    have h' : ((onCount 9 t : ℕ) : ℚ) = 4 := by exact_mod_cast h
    rw [h', he.neg_one_pow]
    ring
  · have h := on_odd t (by rcases ho with ⟨k, rfl⟩; omega) (Nat.odd_iff.mp ho)
    have h' : ((onCount 9 t : ℕ) : ℚ) = 2 * (t : ℚ) - 5 := by exact_mod_cast h
    rw [h', ho.neg_one_pow]
    ring

open OMA.S_oeis_a266250 in
lemma a_succ (n : ℕ) : (a (n + 1) : ℚ) = (a n : ℚ) + ((onCount 9 (n + 1) : ℕ) : ℚ) := by
  unfold a
  rw [Finset.sum_range_succ]
  push_cast
  ring

open OMA.S_oeis_a266250 in
lemma a_three : (a 3 : ℚ) = 5 := by
  have h : a 3 = 5 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a266250 in
lemma a_cl (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℚ) = ((n : ℚ) ^ 2 - (-1 : ℚ) ^ n * ((n : ℚ) - 4) + 2) / 2 := by
  induction n, hn using Nat.le_induction with
  | base => rw [a_three]; norm_num
  | succ n hn2 ih =>
    rw [a_succ, ih, on_big (n + 1) (by omega)]
    push_cast
    ring

open OMA.S_oeis_a266250 in
lemma a_0 : (a 0 : ℚ) = 1 := by
  have h : a 0 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a266250 in
lemma a_1 : (a 1 : ℚ) = 1 := by
  have h : a 1 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a266250 in
lemma a_2 : (a 2 : ℚ) = 3 := by
  have h : a 2 = 3 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a266250 in
lemma a_3 : (a 3 : ℚ) = 5 := by
  rw [a_cl 3 (by norm_num)]; norm_num

open OMA.S_oeis_a266250 in
lemma a_4 : (a 4 : ℚ) = 9 := by
  rw [a_cl 4 (by norm_num)]; norm_num

open OMA.S_oeis_a266250 in
lemma a_5 : (a 5 : ℚ) = 14 := by
  rw [a_cl 5 (by norm_num)]; norm_num

open OMA.S_oeis_a266250 in
lemma a_6 : (a 6 : ℚ) = 18 := by
  rw [a_cl 6 (by norm_num)]; norm_num

open OMA.S_oeis_a266250 in
lemma a_7 : (a 7 : ℚ) = 27 := by
  rw [a_cl 7 (by norm_num)]; norm_num

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A266250Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a266250 A266250Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a266250.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    refine (a_cl n (by omega)).trans ?_
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega]
    rw [a_cl (m + 8) (by omega), a_cl (m + 7) (by omega), a_cl (m + 6) (by omega), a_cl (m + 5) (by omega), a_cl (m + 4) (by omega), a_cl (m + 3) (by omega)]
    push_cast
    ring
  · have hD : ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-1) * PowerSeries.X ^ 1 + PowerSeries.C (-2) * PowerSeries.X ^ 2 + PowerSeries.C 2 * PowerSeries.X ^ 3 + PowerSeries.C 1 * PowerSeries.X ^ 4 + PowerSeries.C (-1) * PowerSeries.X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 2 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 + PowerSeries.X ^ 5 - 2 * PowerSeries.X ^ 6 + PowerSeries.X ^ 7 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 2 * PowerSeries.X ^ 3 + PowerSeries.C 1 * PowerSeries.X ^ 4 + PowerSeries.C 1 * PowerSeries.X ^ 5 + PowerSeries.C (-2) * PowerSeries.X ^ 6 + PowerSeries.C 1 * PowerSeries.X ^ 7 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
    · simp [a_0] <;> norm_num
    · simp [a_0, a_1] <;> norm_num
    · simp [a_0, a_1, a_2] <;> norm_num
    · simp [a_0, a_1, a_2, a_3] <;> norm_num
    · simp [a_0, a_1, a_2, a_3, a_4] <;> norm_num
    · simp [a_0, a_1, a_2, a_3, a_4, a_5] <;> norm_num
    · simp [a_1, a_2, a_3, a_4, a_5, a_6] <;> norm_num
    · simp [a_2, a_3, a_4, a_5, a_6, a_7] <;> norm_num
    · have f0 := a_cl (n + 8) (by omega)
      have f1 := a_cl (n + 7) (by omega)
      have f2 := a_cl (n + 6) (by omega)
      have f3 := a_cl (n + 5) (by omega)
      have f4 := a_cl (n + 4) (by omega)
      have f5 := a_cl (n + 3) (by omega)
      simp [f0, f1, f2, f3, f4, f5]
      ring
