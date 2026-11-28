import OMAStatements.S_oeis_a192252
import Mathlib

namespace A192252Aux

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
lemma a_succ (n : ℕ) : OMA.S_oeis_a192252.a (n + 1) =
    OMA.S_oeis_a192252.a n + ((n + 1).factorial : ℤ) * c (n + 1) := by
  unfold OMA.S_oeis_a192252.a OMA.S_oeis_a192252.p c q
  rw [Finset.sum_range_succ, add_modByMonic, ← smul_eq_C_mul, smul_modByMonic, coeff_add,
    coeff_smul]
  simp

end A192252Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a192252.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 := A192252Aux.a_succ m
  have h2 := A192252Aux.a_succ (m + 1)
  have h3 := A192252Aux.a_succ (m + 2)
  have hc := A192252Aux.c_rec (m + 1)
  have f2 : ((m + 1 + 1).factorial : ℤ) = ((m : ℤ) + 2) * ((m + 1).factorial : ℤ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f3 : ((m + 2 + 1).factorial : ℤ) = ((m : ℤ) + 3) * (((m : ℤ) + 2) * ((m + 1).factorial : ℤ)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  rw [f2] at h2
  rw [f3] at h3
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  have e3 : OMA.S_oeis_a192252.a (m + 3) = OMA.S_oeis_a192252.a (m + 2) +
      ((m : ℤ) + 3) * (((m : ℤ) + 2) * ((m + 1).factorial : ℤ)) * A192252Aux.c (m + 3) := h3
  have e2 : OMA.S_oeis_a192252.a (m + 2) = OMA.S_oeis_a192252.a (m + 1) +
      ((m : ℤ) + 2) * ((m + 1).factorial : ℤ) * A192252Aux.c (m + 2) := h2
  have ec : A192252Aux.c (m + 3) = A192252Aux.c (m + 2) + A192252Aux.c (m + 1) := hc
  rw [e3, ec, e2, h1]
  push_cast
  ring
