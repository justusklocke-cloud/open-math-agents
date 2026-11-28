import OMAStatements.S_oeis_a052731
import Mathlib

namespace A052731Aux

open PowerSeries in
noncomputable def M : PowerSeries ℚ :=
  PowerSeries.mk (fun n => (OMA.S_oeis_a052731.motzkin n : ℚ))

open PowerSeries OMA.S_oeis_a052731 in
lemma hM : M = 1 + X * M + X ^ 2 * M ^ 2 := by
  ext n
  rcases n with _ | _ | n
  · simp [M, motzkin]
  · simp [M, motzkin, coeff_X_pow_mul', coeff_one]
  · show coeff (n + 2) M = coeff (n + 2) (1 + X * M + X ^ 2 * M ^ 2)
    have e1 : coeff (n + 2) (1 : PowerSeries ℚ) = 0 := by
      rw [coeff_one]
      simp
    have e2 : coeff (n + 2) (X * M) = coeff (n + 1) M := coeff_succ_X_mul (n + 1) M
    have e3 : coeff (n + 2) (X ^ 2 * M ^ 2) = coeff n (M ^ 2) := coeff_X_pow_mul (M ^ 2) 2 n
    rw [map_add, map_add, e1, e2, e3, pow_two, coeff_mul]
    simp only [M, coeff_mk]
    rw [motzkin]
    push_cast
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => (motzkin i : ℚ) * (motzkin j : ℚ)) n,
      Fin.sum_univ_eq_sum_range (fun i => (motzkin i : ℚ) * (motzkin (n - i) : ℚ)) (n + 1)]
    ring

open PowerSeries OMA.S_oeis_a052731 in
lemma hD : X * PowerSeries.mk (fun n => (motzkin (n + 1) : ℚ) - (motzkin n : ℚ)) =
    M - 1 - X * M := by
  ext n
  rcases n with _ | n
  · simp [M, motzkin]
  · rw [coeff_succ_X_mul, map_sub, map_sub, coeff_succ_X_mul, coeff_one]
    simp [M]

end A052731Aux

open PowerSeries OMA.S_oeis_a052731 A052731Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a052731.main := by
  refine ⟨1 - X - 2 * X ^ 2 * M, ?_, ?_, ?_⟩
  · simp
  · simp only [map_ofNat]
    linear_combination (-4 * X ^ 2) * hM
  · unfold expectedSeries
    simp only [map_ofNat]
    linear_combination (2 * X ^ 2) * hD
