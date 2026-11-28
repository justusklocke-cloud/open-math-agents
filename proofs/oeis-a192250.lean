import OMAStatements.S_oeis_a192250
import Mathlib

namespace A192250Aux

open Polynomial in
noncomputable def q : ℤ[X] := X ^ 2 - X - 1

open Polynomial in
lemma q_monic : q.Monic := by
  have h : q = X ^ 2 - (X + 1) := by unfold q; ring
  rw [h]
  apply monic_X_pow_sub
  have h1 : degree ((X : ℤ[X]) + 1) = 1 := by
    have := degree_X_add_C (1 : ℤ)
    simpa using this
  rw [h1]
  norm_num

open Polynomial in
noncomputable def c (k : ℕ) : ℤ := ((X : ℤ[X]) ^ k %ₘ q).coeff 0

open Polynomial in
lemma c_rec (k : ℕ) : c (k + 2) = c (k + 1) + c k := by
  unfold c
  have h : (X : ℤ[X]) ^ (k + 2) = X ^ (k + 1) + X ^ k + q * X ^ k := by unfold q; ring
  rw [h, add_modByMonic, add_modByMonic,
    (modByMonic_eq_zero_iff_dvd q_monic).mpr (dvd_mul_right _ _)]
  simp

open Polynomial in
noncomputable def r (n : ℕ) : ℤ := (OMA.S_oeis_a192250.p n %ₘ q).coeff 0

open Polynomial in
lemma r_succ (n : ℕ) : r (n + 1) = r n + ((n + 1).centralBinom : ℤ) * c (n + 1) := by
  unfold r OMA.S_oeis_a192250.p c
  rw [Finset.sum_range_succ, add_modByMonic, ← smul_eq_C_mul, smul_modByMonic, coeff_add,
    coeff_smul]
  simp

lemma a_eq (n : ℕ) : OMA.S_oeis_a192250.a (n + 1) = r n := rfl

end A192250Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a192250.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  simp only [show m + 4 - 1 = m + 2 + 1 by omega, show m + 4 - 2 = m + 1 + 1 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 = m + 3 + 1 by omega, A192250Aux.a_eq]
  have e1 : A192250Aux.r (m + 1) = A192250Aux.r m +
      ((m + 1).centralBinom : ℤ) * A192250Aux.c (m + 1) := A192250Aux.r_succ m
  have e2 : A192250Aux.r (m + 2) = A192250Aux.r (m + 1) +
      ((m + 2).centralBinom : ℤ) * A192250Aux.c (m + 2) := A192250Aux.r_succ (m + 1)
  have e3 : A192250Aux.r (m + 3) = A192250Aux.r (m + 2) +
      ((m + 3).centralBinom : ℤ) * A192250Aux.c (m + 3) := A192250Aux.r_succ (m + 2)
  have ec : A192250Aux.c (m + 3) = A192250Aux.c (m + 2) + A192250Aux.c (m + 1) :=
    A192250Aux.c_rec (m + 1)
  have k2 : ((m : ℤ) + 2) * ((m + 2).centralBinom : ℤ) =
      2 * (2 * (m : ℤ) + 3) * ((m + 1).centralBinom : ℤ) := by
    have := Nat.succ_mul_centralBinom_succ (m + 1)
    have h : (m + 1 + 1) * (m + 2).centralBinom = 2 * (2 * (m + 1) + 1) * (m + 1).centralBinom :=
      this
    have h' := congrArg (fun t : ℕ => (t : ℤ)) h
    push_cast at h'
    linear_combination h'
  have k3 : ((m : ℤ) + 3) * ((m + 3).centralBinom : ℤ) =
      2 * (2 * (m : ℤ) + 5) * ((m + 2).centralBinom : ℤ) := by
    have := Nat.succ_mul_centralBinom_succ (m + 2)
    have h : (m + 2 + 1) * (m + 3).centralBinom = 2 * (2 * (m + 2) + 1) * (m + 2).centralBinom :=
      this
    have h' := congrArg (fun t : ℕ => (t : ℤ)) h
    push_cast at h'
    linear_combination h'
  rw [e3, ec, e2, e1]
  push_cast
  linear_combination ((m : ℤ) + 2) * (A192250Aux.c (m + 2) + A192250Aux.c (m + 1)) * k3 +
    2 * (2 * (m : ℤ) + 5) * A192250Aux.c (m + 1) * k2
