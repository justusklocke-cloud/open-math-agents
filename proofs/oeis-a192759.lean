import OMAStatements.S_oeis_a192759
import Mathlib

namespace A192759
open Polynomial

/-- The constant added in step n of the recursion for p. -/
def cc (n : ℕ) : ℤ := ((((n + 1) + 5) / 5 : ℕ) : ℤ)

/-- The pair (constant coefficient, coefficient of X) of the reduction of p n. -/
def uv : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((uv n).2 + cc n, (uv n).1 + (uv n).2)

lemma cc_shift (n : ℕ) : cc (n + 5) = cc n + 1 := by
  unfold cc
  have h : ((n + 5 + 1) + 5) / 5 = ((n + 1) + 5) / 5 + 1 := by omega
  rw [h]; push_cast; ring

lemma cc_succ (n : ℕ) : cc (n + 1) = cc n + (if (n + 2) % 5 = 0 then 1 else 0) := by
  unfold cc
  have h : ((n + 1 + 1) + 5) / 5 = ((n + 1) + 5) / 5 + (if (n + 2) % 5 = 0 then 1 else 0) := by
    split_ifs <;> omega
  rw [h]; push_cast; ring

lemma p_eq (n : ℕ) : ∃ q : ℤ[X], OMA.S_oeis_a192759.p n
    = (X ^ 2 - X - 1) * q + (C (uv n).1 + C (uv n).2 * X) := by
  induction n with
  | zero => exact ⟨0, by simp [OMA.S_oeis_a192759.p, uv]⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨X * q + C (uv n).2, ?_⟩
    rw [OMA.S_oeis_a192759.p, hq, uv, cc]
    simp only [map_add]
    ring

lemma monicQ : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  have h : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + C 1) := by simp only [map_one]; ring
  rw [h]
  apply monic_X_pow_sub
  rw [degree_X_add_C]
  decide

lemma mod_coeff (f q : ℤ[X]) (u v : ℤ) (h : f = (X ^ 2 - X - 1) * q + (C u + C v * X)) :
    (f %ₘ (X ^ 2 - X - 1)).coeff 1 = v := by
  have hdeg : (C u + C v * X : ℤ[X]).degree < (X ^ 2 - X - 1 : ℤ[X]).degree := by
    have h1 : (C u + C v * X : ℤ[X]).degree ≤ 1 := by compute_degree
    have h2 : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by compute_degree!
    rw [h2]
    exact lt_of_le_of_lt h1 (by decide)
  have := (div_modByMonic_unique (f := f) q (C u + C v * X) monicQ ⟨by rw [h]; ring, hdeg⟩).2
  rw [this, coeff_add, coeff_C_mul, coeff_X_one, coeff_C]
  simp

lemma a_eq (n : ℕ) : OMA.S_oeis_a192759.a n = (uv n).2 := by
  obtain ⟨q, hq⟩ := p_eq n
  exact mod_coeff _ q _ _ hq

lemma inv (n : ℕ) : (uv n).1 = OMA.S_oeis_a192759.A124502 (n + 1) ∧
    (uv n).2 = ∑ k ∈ Finset.Icc 1 n, OMA.S_oeis_a192759.A124502 k ∧
    OMA.S_oeis_a192759.A124502 (n + 2)
      = (∑ k ∈ Finset.Icc 1 n, OMA.S_oeis_a192759.A124502 k) + cc n := by
  induction n with
  | zero => simp [uv, OMA.S_oeis_a192759.A124502, cc]
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hs : ∑ k ∈ Finset.Icc 1 (n + 1), OMA.S_oeis_a192759.A124502 k
        = (∑ k ∈ Finset.Icc 1 n, OMA.S_oeis_a192759.A124502 k)
          + OMA.S_oeis_a192759.A124502 (n + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    have hA : OMA.S_oeis_a192759.A124502 (n + 3) = OMA.S_oeis_a192759.A124502 (n + 2)
        + OMA.S_oeis_a192759.A124502 (n + 1) + (if (n + 2) % 5 = 0 then 1 else 0) := by
      rw [OMA.S_oeis_a192759.A124502]
    refine ⟨?_, ?_, ?_⟩
    · rw [uv]; simp only; rw [h2, h3]
    · rw [uv]; simp only; rw [h1, h2, hs]; ring
    · rw [hA, hs, cc_succ, h3]; ring

end A192759

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a192759.main := by
  constructor
  · have ha : OMA.S_oeis_a192759.a = fun n => (A192759.uv n).2 := funext A192759.a_eq
    rw [ha]
    have hD : (((X : PowerSeries ℤ) ^ 2 + X - 1) * (X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X - 1) ^ 2)
        = C (-1) * X ^ 0 + C 2 * X ^ 1 + C (-1) * X ^ 3 + C 1 * X ^ 5 + C (-2) * X ^ 6
          + C 1 * X ^ 8 := by
      simp only [map_neg, map_ofNat, map_one]; ring
    have hN : -(X : PowerSeries ℤ) = C (-1) * X ^ 1 := by
      simp only [map_neg, map_one]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, ← mul_assoc, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_C,
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
    · simp [A192759.uv]
    · simp [A192759.uv, A192759.cc]
    · simp [A192759.uv, A192759.cc]
    · simp [A192759.uv, A192759.cc]
    · simp [A192759.uv, A192759.cc]
    · simp [A192759.uv, A192759.cc]
    · simp [A192759.uv, A192759.cc]
    · simp [A192759.uv, A192759.cc]
    · have h5 := A192759.cc_shift n
      have h6 : A192759.cc (n + 6) = A192759.cc (n + 1) + 1 := A192759.cc_shift (n + 1)
      simp [A192759.uv]
      rw [h5, h6]
      ring
  · intro n
    rw [A192759.a_eq]
    exact (A192759.inv n).2.1
