import OMAStatements.S_oeis_a258902
import Mathlib

namespace A258902Aux

open PowerSeries

lemma ode (A : PowerSeries ℚ)
    (hA : A - C (1 / 2 : ℚ) * A ^ 2 - C (1 / 3 : ℚ) * A ^ 3 = X) :
    (19 - 42 * X - 36 * X ^ 2) * derivative ℚ (derivative ℚ A) - (21 + 36 * X) * derivative ℚ A
      + 4 * A + 2 = 0 := by
  have f2 : (2 : PowerSeries ℚ) * C (1 / 2 : ℚ) = 1 := by
    rw [← map_ofNat C 2, ← map_mul]
    norm_num
  have f3 : (3 : PowerSeries ℚ) * C (1 / 3 : ℚ) = 1 := by
    rw [← map_ofNat C 3, ← map_mul]
    norm_num
  have f36 : C (1 / 36 : ℚ) * (36 : PowerSeries ℚ) = 1 := by
    rw [← map_ofNat C 36, ← map_mul]
    norm_num
  have hA' : A - C (1 / 2 : ℚ) * (A * A) - C (1 / 3 : ℚ) * (A * A * A) = X := by
    rw [← hA]
    ring
  have hX6 : 6 * X = 6 * A - 3 * A ^ 2 - 2 * A ^ 3 := by
    linear_combination (-6 : PowerSeries ℚ) * hA - 3 * A ^ 2 * f2 - 2 * A ^ 3 * f3
  have h1 : (1 - A - A * A) * derivative ℚ A = 1 := by
    have e := congrArg (derivative ℚ) hA'
    simp only [map_sub, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul] at e
    linear_combination e + (A * derivative ℚ A) * f2 + (A * A * derivative ℚ A) * f3
  have h2 : (1 - A - A * A) * derivative ℚ (derivative ℚ A) =
      (1 + 2 * A) * derivative ℚ A ^ 2 := by
    have e := congrArg (derivative ℚ) h1
    simp only [map_sub, Derivation.leibniz, smul_eq_mul, Derivation.map_one_eq_zero] at e
    linear_combination e
  have key : 36 * ((19 - 42 * X - 36 * X ^ 2) * derivative ℚ (derivative ℚ A)
      - (21 + 36 * X) * derivative ℚ A + 4 * A + 2) = 0 := by
    have hD3 : ((1 - A - A * A) * derivative ℚ A) ^ 3 = 1 := by rw [h1]; ring
    have big : 36 * (1 - A - A * A) ^ 3 * ((19 - 42 * X - 36 * X ^ 2) * derivative ℚ (derivative ℚ A)
        - (21 + 36 * X) * derivative ℚ A + 4 * A + 2) = 0 := by
      linear_combination (36 * (19 - 42 * X - 36 * X ^ 2) * (1 - A - A * A) ^ 2) * h2
        + (36 * (19 - 42 * X - 36 * X ^ 2) * (1 + 2 * A) * ((1 - A - A * A) * derivative ℚ A + 1)
            - 36 * (21 + 36 * X) * (1 - A - A * A) ^ 2) * h1
        + (-252 * (1 + 2 * A) - 216 * (1 - A - A * A) ^ 2 - 216 * (1 + 2 * A) * X
            - 36 * (1 + 2 * A) * (6 * A - 3 * A ^ 2 - 2 * A ^ 3)) * hX6
    linear_combination (derivative ℚ A ^ 3) * big
      - (36 * ((19 - 42 * X - 36 * X ^ 2) * derivative ℚ (derivative ℚ A)
        - (21 + 36 * X) * derivative ℚ A + 4 * A + 2)) * hD3
  linear_combination (C (1 / 36 : ℚ)) * key
    - ((19 - 42 * X - 36 * X ^ 2) * derivative ℚ (derivative ℚ A)
      - (21 + 36 * X) * derivative ℚ A + 4 * A + 2) * f36

lemma coeff_rec (A : PowerSeries ℚ)
    (hA : A - C (1 / 2 : ℚ) * A ^ 2 - C (1 / 3 : ℚ) * A ^ 3 = X) (k : ℕ) :
    19 * (coeff (k + 3) A * ((k : ℚ) + 3) * ((k : ℚ) + 2))
      = 21 * (2 * (k : ℚ) + 3) * (coeff (k + 2) A * ((k : ℚ) + 2))
        + 4 * (3 * (k : ℚ) + 4) * (3 * (k : ℚ) + 2) * coeff (k + 1) A := by
  have h := ode A hA
  have e2 : (C 2 : PowerSeries ℚ) = 2 := map_ofNat C 2
  have e4 : (C 4 : PowerSeries ℚ) = 4 := map_ofNat C 4
  have e19 : (C 19 : PowerSeries ℚ) = 19 := map_ofNat C 19
  have e21 : (C 21 : PowerSeries ℚ) = 21 := map_ofNat C 21
  have e36 : (C 36 : PowerSeries ℚ) = 36 := map_ofNat C 36
  have e42 : (C 42 : PowerSeries ℚ) = 42 := map_ofNat C 42
  have h' : C 19 * derivative ℚ (derivative ℚ A) + C 4 * A + C 2 =
      C 42 * (X * derivative ℚ (derivative ℚ A)) + C 36 * (X * (X * derivative ℚ (derivative ℚ A)))
        + C 21 * derivative ℚ A + C 36 * (X * derivative ℚ A) := by
    rw [e2, e4, e19, e21, e36, e42]
    linear_combination h
  have d2 : ∀ j, coeff j (derivative ℚ (derivative ℚ A)) =
      coeff (j + 2) A * ((j : ℚ) + 2) * ((j : ℚ) + 1) := by
    intro j
    rw [coeff_derivative, coeff_derivative]
    push_cast
    ring
  have d1 : ∀ j, coeff j (derivative ℚ A) = coeff (j + 1) A * ((j : ℚ) + 1) := by
    intro j
    rw [coeff_derivative]
  have hx : coeff k (X * derivative ℚ (derivative ℚ A)) =
      coeff (k + 1) A * ((k : ℚ) + 1) * (k : ℚ) := by
    rcases k with _ | m
    · rw [coeff_zero_X_mul]
      simp
    · rw [coeff_succ_X_mul, d2]
      push_cast
      ring
  have hc := congrArg (coeff (k + 1)) h'
  rw [map_add, map_add, map_add, map_add, map_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    coeff_C_mul, coeff_C_mul, coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul, hx, d2, d2, d1, d1,
    coeff_C, if_neg (by omega)] at hc
  push_cast at hc
  linear_combination hc

end A258902Aux

open PowerSeries OMA.S_oeis_a258902 A258902Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a258902.main := by
  intro A _ hA n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 from by omega, show k + 3 - 2 = k + 1 from by omega]
  unfold a
  have h := coeff_rec A hA k
  have f3 : ((k + 3).factorial : ℚ) = ((k : ℚ) + 3) * ((k : ℚ) + 2) * ((k + 1).factorial : ℚ) := by
    rw [Nat.factorial_succ (k + 2), Nat.factorial_succ (k + 1)]
    push_cast
    ring
  have f2 : ((k + 2).factorial : ℚ) = ((k : ℚ) + 2) * ((k + 1).factorial : ℚ) := by
    rw [Nat.factorial_succ (k + 1)]
    push_cast
    ring
  rw [f3, f2]
  push_cast
  linear_combination ((k + 1).factorial : ℚ) * h
