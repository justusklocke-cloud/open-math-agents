import OMAStatements.S_oeis_a223907
import Mathlib

namespace A223907Aux

open OMA.S_oeis_a223907 in
lemma a_cl (n : ℕ) : a n = 6 * 2 ^ n + 11 * 3 ^ n + 6 * 4 ^ n + 5 ^ n := by
  have h0 : Nat.stirlingFirst 4 0 = 0 := by decide
  have h1 : Nat.stirlingFirst 4 1 = 6 := by decide
  have h2 : Nat.stirlingFirst 4 2 = 11 := by decide
  have h3 : Nat.stirlingFirst 4 3 = 6 := by decide
  have h4 : Nat.stirlingFirst 4 4 = 1 := by decide
  unfold a hatc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4]
  push_cast
  ring

open PowerSeries in
lemma coeff_term (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A223907Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a223907 A223907Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a223907.main := by
  refine ⟨?_, ?_⟩
  · intro n _
    rw [a_cl]
    have h4 : (4 : ℤ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
    rw [h4]
    ring
  · have hD : ((2 * PowerSeries.X - 1) * (3 * PowerSeries.X - 1) * (4 * PowerSeries.X - 1) *
        (5 * PowerSeries.X - 1) : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-14) * PowerSeries.X ^ 1 +
        PowerSeries.C 71 * PowerSeries.X ^ 2 + PowerSeries.C (-154) * PowerSeries.X ^ 3 +
        PowerSeries.C 120 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (-2 * PowerSeries.X * (1440 * PowerSeries.X ^ 3 - 1346 * PowerSeries.X ^ 2 +
        396 * PowerSeries.X - 37) : PowerSeries ℤ) =
        PowerSeries.C 74 * PowerSeries.X ^ 1 + PowerSeries.C (-792) * PowerSeries.X ^ 2 +
        PowerSeries.C 2692 * PowerSeries.X ^ 3 + PowerSeries.C (-2880) * PowerSeries.X ^ 4 := by
      simp only [map_ofNat, map_neg]; ring
    unfold A
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | n
    · simp
    · simp [a_cl]
    · simp [a_cl]
    · simp [a_cl]
    · simp [a_cl]
    · simp [a_cl]
      ring
