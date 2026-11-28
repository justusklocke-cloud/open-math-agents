import OMAStatements.S_oeis_a052736
import Mathlib

namespace A052736Aux

open PowerSeries in
lemma royal_coeff_zero : coeff 0 OMA.S_oeis_a052736.royalSeries = (1 : ℚ) := by
  unfold OMA.S_oeis_a052736.royalSeries
  rw [coeff_zero_eq_constantCoeff_apply, map_mul]
  simp [OMA.S_oeis_a052736.largeSchroeder]

open PowerSeries in
lemma sq_coeff_one (root : PowerSeries ℚ) (h0 : coeff 0 root = 1) :
    coeff 1 (root ^ 2) = 2 * coeff 1 root := by
  rw [pow_two, coeff_mul]
  rw [Finset.Nat.antidiagonal_succ]
  simp [h0]
  ring

end A052736Aux

open PowerSeries A052736Aux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a052736.main) := by
  rintro ⟨root, h0, hsq, hid⟩
  have hc0 : coeff 0 root = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply]; exact h0
  have h1 := congrArg (coeff 1) hsq
  rw [sq_coeff_one root hc0] at h1
  have hr : coeff 1 ((1 : PowerSeries ℚ) - C 6 * X + X ^ 2) = -6 := by
    simp [coeff_one, coeff_X_pow]
  rw [hr] at h1
  have h2 := congrArg (coeff 1) hid
  have hl : coeff 1 (C (2 : ℚ) * X * OMA.S_oeis_a052736.royalSeries) = 2 := by
    rw [mul_assoc, coeff_C_mul, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
      royal_coeff_zero]
    norm_num
  have hrr : coeff 1 ((1 : PowerSeries ℚ) - C 3 * X - root - X * (1 - X - root))
      = -3 - coeff 1 root := by
    rw [map_sub, map_sub, map_sub, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]
    simp [coeff_one, h0]
  rw [hl, hrr] at h2
  linarith
