import OMAStatements.S_oeis_a001845
import Mathlib

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a001845.main := by
  have hD : ((1 : PowerSeries ℚ) - X) ^ 4
      = C 1 * X ^ 0 + C (-4) * X ^ 1 + C 6 * X ^ 2 + C (-4) * X ^ 3 + C 1 * X ^ 4 := by
    simp only [map_neg, map_ofNat, map_one]; ring
  have hN : ((1 : PowerSeries ℚ) + X) ^ 3
      = C 1 * X ^ 0 + C 3 * X ^ 1 + C 3 * X ^ 2 + C 1 * X ^ 3 := by
    simp only [map_ofNat, map_one]; ring
  rw [hD, hN]
  ext n
  simp only [mul_add, map_add, ← mul_assoc, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_C,
    PowerSeries.coeff_mk]
  rcases n with _ | _ | _ | _ | n
  · simp [OMA.S_oeis_a001845.a]
  · simp [OMA.S_oeis_a001845.a]; norm_num
  · simp [OMA.S_oeis_a001845.a]; norm_num
  · simp [OMA.S_oeis_a001845.a]; norm_num
  · simp [OMA.S_oeis_a001845.a]; ring
