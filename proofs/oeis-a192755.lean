import OMAStatements.S_oeis_a192755
import Mathlib

namespace A192755
open Polynomial

/-- The pair (constant coefficient, coefficient of X) of the reduction of p n. -/
def uv : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((uv n).2 + (5 * ((n : ℤ) + 1) + 1), (uv n).1 + (uv n).2)

lemma p_eq (n : ℕ) : ∃ q : ℤ[X], OMA.S_oeis_a192755.p n
    = (X ^ 2 - X - 1) * q + (C (uv n).1 + C (uv n).2 * X) := by
  induction n with
  | zero => exact ⟨0, by simp [OMA.S_oeis_a192755.p, uv]⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨X * q + C (uv n).2, ?_⟩
    rw [OMA.S_oeis_a192755.p, hq, uv]
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

lemma a_eq (n : ℕ) : OMA.S_oeis_a192755.a n = (uv n).2 := by
  obtain ⟨q, hq⟩ := p_eq n
  exact mod_coeff _ q _ _ hq

end A192755

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a192755.main := by
  have ha : OMA.S_oeis_a192755.a = fun n => (A192755.uv n).2 := funext A192755.a_eq
  rw [ha]
  have hD : (((X : PowerSeries ℤ) ^ 2 + X - 1) * (X - 1) ^ 2)
      = C (-1) * X ^ 0 + C 3 * X ^ 1 + C (-2) * X ^ 2 + C (-1) * X ^ 3 + C 1 * X ^ 4 := by
    simp only [map_neg, map_ofNat, map_one]; ring
  have hN : -(X : PowerSeries ℤ) * (1 + 4 * X) = C (-1) * X ^ 1 + C (-4) * X ^ 2 := by
    simp only [map_neg, map_ofNat, map_one]; ring
  rw [hD, hN]
  ext n
  simp only [mul_add, map_add, ← mul_assoc, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_C,
    PowerSeries.coeff_mk, PowerSeries.coeff_C]
  rcases n with _ | _ | _ | _ | n
  · simp [A192755.uv]
  · simp [A192755.uv]
  · simp [A192755.uv]
  · simp [A192755.uv]
  · simp [A192755.uv]; ring
