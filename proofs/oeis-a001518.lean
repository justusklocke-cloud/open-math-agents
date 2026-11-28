import OMAStatements.S_oeis_a001518
import Mathlib

namespace A001518Aux

open PowerSeries

lemma ode_unique (V : PowerSeries ℚ)
    (h : derivative ℚ (derivative ℚ V) =
      C 9 * derivative ℚ V + V + C 6 * (X * derivative ℚ (derivative ℚ V)))
    (h0 : coeff 0 V = 0) (h1 : coeff 1 V = 0) : V = 0 := by
  have c2 : ∀ k, coeff k (derivative ℚ (derivative ℚ V)) =
      coeff (k + 2) V * ((k : ℚ) + 2) * ((k : ℚ) + 1) := by
    intro k
    rw [coeff_derivative, coeff_derivative]
    push_cast
    ring
  have c1 : ∀ k, coeff k (derivative ℚ V) = coeff (k + 1) V * ((k : ℚ) + 1) := by
    intro k
    rw [coeff_derivative]
  have key : ∀ n, coeff n V = 0 ∧ coeff (n + 1) V = 0 := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have e := congrArg (coeff n) h
      rcases n with _ | m
      · rw [map_add, map_add, coeff_C_mul, coeff_C_mul, coeff_zero_X_mul, c2, c1] at e
        rw [h1, h0] at e
        norm_num at e
        exact e
      · rw [map_add, map_add, coeff_C_mul, coeff_C_mul, coeff_succ_X_mul, c2, c1, c2] at e
        rw [ih.1, ih.2] at e
        have hpos : (((m + 1 : ℕ) : ℚ) + 2) * (((m + 1 : ℕ) : ℚ) + 1) ≠ 0 := by positivity
        have e' : coeff (m + 1 + 2) V * ((((m + 1 : ℕ) : ℚ) + 2) * (((m + 1 : ℕ) : ℚ) + 1)) = 0 := by
          linarith
        rcases mul_eq_zero.mp e' with h' | h'
        · exact h'
        · exact absurd h' hpos
  ext n
  simpa using (key n).1

lemma key (N D G : PowerSeries ℚ)
    (hD : derivative ℚ D = N)
    (hN : derivative ℚ N = C 3 * N + D + C 6 * (X * derivative ℚ N))
    (hG : derivative ℚ G = C 3 * G + C 6 * (X * derivative ℚ G))
    (h0 : coeff 0 N = coeff 0 (G * D)) (h1 : coeff 1 N = coeff 1 (G * D)) :
    N = G * D := by
  have e3 : (C 3 : PowerSeries ℚ) = 3 := map_ofNat C 3
  have e6 : (C 6 : PowerSeries ℚ) = 6 := map_ofNat C 6
  have e9 : (C 9 : PowerSeries ℚ) = 9 := map_ofNat C 9
  have d3 : derivative ℚ (3 : PowerSeries ℚ) = 0 := by rw [← e3]; exact derivative_C
  have d6 : derivative ℚ (6 : PowerSeries ℚ) = 0 := by rw [← e6]; exact derivative_C
  rw [e3, e6] at hN hG
  have hN2 : derivative ℚ (derivative ℚ N) =
      9 * derivative ℚ N + N + 6 * (X * derivative ℚ (derivative ℚ N)) := by
    have e := congrArg (derivative ℚ) hN
    simp only [map_add, Derivation.leibniz, derivative_X, smul_eq_mul, hD, d3, d6] at e
    linear_combination e
  have hG2 : derivative ℚ (derivative ℚ G) =
      9 * derivative ℚ G + 6 * (X * derivative ℚ (derivative ℚ G)) := by
    have e := congrArg (derivative ℚ) hG
    simp only [map_add, Derivation.leibniz, derivative_X, smul_eq_mul, d3, d6] at e
    linear_combination e
  have hZ1 : derivative ℚ (G * D) = G * N + D * derivative ℚ G := by
    simp only [Derivation.leibniz, smul_eq_mul, hD]
  have hZ2 : derivative ℚ (derivative ℚ (G * D)) =
      G * derivative ℚ N + 2 * (N * derivative ℚ G) + D * derivative ℚ (derivative ℚ G) := by
    rw [hZ1]
    simp only [map_add, Derivation.leibniz, smul_eq_mul, hD]
    ring
  have hV : N - G * D = 0 := by
    apply ode_unique
    · rw [map_sub, map_sub, hZ2, hZ1, e9, e6]
      linear_combination hN2 - G * hN - 2 * N * hG - D * hG2
    · rw [map_sub, h0, sub_self]
    · rw [map_sub, h1, sub_self]
  exact sub_eq_zero.mp hV

end A001518Aux

open PowerSeries OMA.S_oeis_a001518 A001518Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a001518.main := by
  have hfac : ∀ n : ℕ, ((n.factorial : ℚ)) ≠ 0 := fun n => by positivity
  have hmain := key (PowerSeries.mk fun n => besselAtThree n / (n.factorial : ℚ))
    (1 + X * PowerSeries.mk (fun n => besselAtThree n / ((n + 1).factorial : ℚ)))
    (PowerSeries.mk (fun n => sextupleFactorial n / (n.factorial : ℚ)))
    (by
      ext n
      rw [coeff_derivative, map_add, coeff_succ_X_mul, coeff_mk, coeff_mk, coeff_one]
      simp only [Nat.succ_ne_zero, if_false, zero_add]
      rw [Nat.factorial_succ]
      have := hfac n
      push_cast
      field_simp)
    (by
      ext n
      rcases n with _ | n
      · rw [coeff_derivative, map_add, map_add, coeff_C_mul, coeff_C_mul, coeff_zero_X_mul,
          map_add, coeff_zero_X_mul, coeff_mk, coeff_mk, coeff_one]
        simp [besselAtThree]
        norm_num
      · rw [coeff_derivative, map_add, map_add, coeff_C_mul, coeff_C_mul, coeff_succ_X_mul,
          map_add, coeff_succ_X_mul, coeff_derivative, coeff_mk, coeff_mk, coeff_mk, coeff_one]
        simp only [Nat.succ_ne_zero, if_false, zero_add]
        rw [show besselAtThree (n + 1 + 1) = 3 * (2 * (n : ℚ) + 3) * besselAtThree (n + 1)
          + besselAtThree n from by rw [besselAtThree]]
        rw [show (n + 1 + 1).factorial = (n + 2) * (n + 1).factorial from Nat.factorial_succ (n + 1)]
        have := hfac (n + 1)
        push_cast
        field_simp
        ring)
    (by
      ext n
      rcases n with _ | n
      · rw [coeff_derivative, map_add, coeff_C_mul, coeff_C_mul, coeff_zero_X_mul,
          coeff_mk, coeff_mk]
        simp [sextupleFactorial]
      · rw [coeff_derivative, map_add, coeff_C_mul, coeff_C_mul, coeff_succ_X_mul,
          coeff_derivative, coeff_mk, coeff_mk]
        rw [show sextupleFactorial (n + 1 + 1) = sextupleFactorial (n + 1) * (6 * ((n + 1 : ℕ) : ℚ) + 3)
          from by unfold sextupleFactorial; rw [Finset.prod_range_succ]]
        rw [show (n + 1 + 1).factorial = (n + 2) * (n + 1).factorial from Nat.factorial_succ (n + 1)]
        have := hfac (n + 1)
        push_cast
        field_simp
        ring)
    (by
      rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul]
      simp [besselAtThree, sextupleFactorial])
    (by
      have hx : coeff 1 (X * PowerSeries.mk (fun n => besselAtThree n / ((n + 1).factorial : ℚ))) =
          besselAtThree 0 / ((0 + 1).factorial : ℚ) := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_mk]
      rw [coeff_one_mul, map_add (coeff 1), hx]
      simp [besselAtThree, sextupleFactorial, coeff_one]
      norm_num)
  rw [hmain, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp), mul_one]
