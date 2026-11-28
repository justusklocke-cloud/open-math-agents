import OMAStatements.S_oeis_a267604
import Mathlib

namespace A267604Aux

open OMA.S_oeis_a267604 in
lemma rule_iff (l c r : Bool) : rule l c r = true ↔
    ((¬ l = true ∧ ¬ c = true ∧ ¬ r = true) ∨ (¬ l = true ∧ ¬ c = true ∧ r = true) ∨ (¬ l = true ∧ c = true ∧ ¬ r = true) ∨ (¬ l = true ∧ c = true ∧ r = true) ∨ (l = true ∧ ¬ c = true ∧ r = true) ∨ (l = true ∧ c = true ∧ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

open OMA.S_oeis_a267604 in
lemma s0 (i : ℤ) : row 0 i = true ↔ i = 0 := by
  simp [row]

open OMA.S_oeis_a267604 in
lemma s1 (i : ℤ) : row 1 i = true ↔ ¬(i = 1) := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, row, rule_iff]
  simp only [s0]
  omega

open OMA.S_oeis_a267604 in
lemma sgen (t : ℕ) (ht : 1 ≤ t) : ∀ i : ℤ, row t i = true ↔ ¬(i = 2 - (t : ℤ)) := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro i
    rw [s1]
    norm_num
  | succ t ht ih =>
    intro i
    rw [row, rule_iff]
    simp only [ih]
    push_cast
    omega

open OMA.S_oeis_a267604 in
lemma mid_on (t : ℕ) (ht : 3 ≤ t) : row t 0 = true := by
  rw [sgen t (by omega)]
  omega

open OMA.S_oeis_a267604 in
lemma a_succ (n : ℕ) : a (n + 1) = 2 * a n + (if row (n + 1) 0 = true then 1 else 0) := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum]
  simp only [Nat.sub_self, pow_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have h1 : t < n + 1 := Finset.mem_range.mp ht
  have h2 : n + 1 - t = (n - t) + 1 := by omega
  rw [h2]
  split_ifs
  · ring
  · ring

open OMA.S_oeis_a267604 in
lemma a_nat (m : ℕ) : a (m + 2) + 1 = 7 * 2 ^ m := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 by ring, a_succ, if_pos (mid_on (m + 2 + 1) (by omega)), pow_succ]
    omega

open OMA.S_oeis_a267604 in
lemma a_int (m : ℕ) : ((a (m + 2) : ℕ) : ℤ) = 7 * 2 ^ m - 1 := by
  have h := a_nat m
  have h2 : ((a (m + 2) : ℕ) : ℤ) + 1 = 7 * 2 ^ m := by exact_mod_cast h
  linarith

open OMA.S_oeis_a267604 in
lemma a_rec (m : ℕ) : ((a (m + 4) : ℕ) : ℤ) = 3 * a (m + 3) - 2 * a (m + 2) := by
  have h4 := a_int (m + 2)
  have h3 := a_int (m + 1)
  have h2 := a_int m
  rw [show m + 1 + 2 = m + 3 by ring] at h3
  rw [show m + 2 + 2 = m + 4 by ring] at h4
  rw [h4, h3, h2]
  ring

open OMA.S_oeis_a267604 in
lemma a_0 : ((a 0 : ℕ) : ℤ) = 1 := by
  have h : a 0 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267604 in
lemma a_1 : ((a 1 : ℕ) : ℤ) = 3 := by
  have h : a 1 = 3 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a267604 in
lemma a_2 : ((a 2 : ℕ) : ℤ) = 6 := by
  have h := a_int 0
  norm_num at h
  exact h

open OMA.S_oeis_a267604 in
lemma a_3 : ((a 3 : ℕ) : ℤ) = 13 := by
  have h := a_int 1
  norm_num at h
  exact h

open PowerSeries in
lemma coeff_term (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267604Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267604 A267604Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a267604.main := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
    exact a_rec m
  · have hD : ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-3) * PowerSeries.X ^ 1 + PowerSeries.C 2 * PowerSeries.X ^ 2 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-1) * PowerSeries.X ^ 2 + PowerSeries.C 1 * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | n
    · simp [a_0] <;> norm_num
    · simp [a_0, a_1] <;> norm_num
    · simp [a_0, a_1, a_2] <;> norm_num
    · simp [a_1, a_2, a_3] <;> norm_num
    · have h := a_rec n
      simp
      linarith
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 2 = m by omega]
    unfold A086224
    have h := a_nat m
    omega
  · intro n
    rcases n with _ | _ | m
    · rw [a_0, eq_comm, Int.ceil_eq_iff]
      norm_num
    · rw [a_1, eq_comm, Int.ceil_eq_iff]
      norm_num
    · have e : (7 / 4 : ℚ) * 2 ^ (m + 1 + 1) - 1 = ((7 * 2 ^ m - 1 : ℤ) : ℚ) := by
        push_cast
        ring
      rw [e, Int.ceil_intCast]
      exact a_int m
