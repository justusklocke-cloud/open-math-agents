import OMAStatements.S_oeis_a192251
import Mathlib

namespace A192251
open OMA.S_oeis_a192251
open Polynomial

lemma q_monic : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  have h : (X ^ 2 - X - 1 : ℤ[X]) = X ^ (1 + 1) - (X + 1) := by ring
  rw [h]
  apply monic_X_pow_sub
  have : degree (X + 1 : ℤ[X]) ≤ 1 := by compute_degree
  exact lt_of_le_of_lt this (by norm_num)

lemma q_degree : degree (X ^ 2 - X - 1 : ℤ[X]) = 2 := by
  compute_degree!

lemma red_eq (f s : ℤ[X]) (u v : ℤ) (h : f = (X ^ 2 - X - 1) * s + (C u + C v * X)) :
    f %ₘ (X ^ 2 - X - 1) = C u + C v * X := by
  have hdeg : degree (C u + C v * X : ℤ[X]) < degree (X ^ 2 - X - 1 : ℤ[X]) := by
    rw [q_degree]
    have : degree (C u + C v * X : ℤ[X]) ≤ 1 := by compute_degree
    exact lt_of_le_of_lt this (by norm_num)
  have hsum : (C u + C v * X) + (X ^ 2 - X - 1) * s = f := by rw [h]; ring
  exact (div_modByMonic_unique s (C u + C v * X) q_monic ⟨hsum, hdeg⟩).2

lemma coeff_one_lin (u v : ℤ) : (C u + C v * X : ℤ[X]).coeff 1 = v := by
  rw [coeff_add, coeff_C_mul, coeff_X_one, coeff_C_of_ne_zero (by norm_num)]
  ring

lemma coeff_zero_lin (u v : ℤ) : (C u + C v * X : ℤ[X]).coeff 0 = u := by
  rw [coeff_add, coeff_C_mul, coeff_X_zero, coeff_C_zero]
  ring

/-- x^k reduces to fu(k).1 + fu(k).2 x (shifted Fibonacci numbers). -/
def fu : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((fu n).2, (fu n).1 + (fu n).2)

lemma xpow_red (k : ℕ) :
    ∃ s : ℤ[X], (X : ℤ[X]) ^ k = (X ^ 2 - X - 1) * s + (C (fu k).1 + C (fu k).2 * X) := by
  induction k with
  | zero =>
    refine ⟨0, ?_⟩
    simp [fu]
  | succ k ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨X * s + C (fu k).2, ?_⟩
    rw [pow_succ, hs]
    simp only [fu, map_add]
    ring

lemma f_rec (k : ℕ) : (fu (k + 2)).2 = (fu (k + 1)).2 + (fu k).2 := by
  simp only [fu]
  ring

/-- The pair (constant term, coefficient of x) of the reduction of p(n,x). -/
def PV : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => ((PV n).1 + ((n + 1).centralBinom : ℤ) * (fu (n + 1)).1,
      (PV n).2 + ((n + 1).centralBinom : ℤ) * (fu (n + 1)).2)

lemma p_succ (n : ℕ) : p (n + 1) = p n + C (((n + 1).centralBinom : ℤ)) * X ^ (n + 1) := by
  unfold p
  rw [Finset.sum_range_succ]

lemma p_zero : p 0 = 1 := by
  unfold p
  simp

lemma p_red (n : ℕ) : ∃ s : ℤ[X], p n = (X ^ 2 - X - 1) * s + (C (PV n).1 + C (PV n).2 * X) := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    rw [p_zero]
    simp [PV]
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    obtain ⟨t, ht⟩ := xpow_red (n + 1)
    refine ⟨s + C (((n + 1).centralBinom : ℤ)) * t, ?_⟩
    rw [p_succ, hs, ht]
    simp only [PV, map_add, map_mul]
    ring

lemma a_eq (n : ℕ) : a (n + 1) = (PV n).2 := by
  obtain ⟨s, hs⟩ := p_red n
  unfold a
  rw [show n + 1 - 1 = n by omega, red_eq _ s _ _ hs, coeff_one_lin]

lemma PV_succ (n : ℕ) :
    (PV (n + 1)).2 = (PV n).2 + ((n + 1).centralBinom : ℤ) * (fu (n + 1)).2 := by
  simp only [PV]

lemma cb_step (k : ℕ) :
    ((k : ℤ) + 1) * ((k + 1).centralBinom : ℤ) = 2 * (2 * (k : ℤ) + 1) * (k.centralBinom : ℤ) := by
  have h := Nat.succ_mul_centralBinom_succ k
  have h' : (((k + 1) * (k + 1).centralBinom : ℕ) : ℤ) = ((2 * (2 * k + 1) * k.centralBinom : ℕ) : ℤ) := by
    rw [h]
  push_cast at h'
  exact h'

lemma key (m : ℕ) :
    ((m : ℤ) + 3) * ((m : ℤ) + 2) * (PV (m + 3)).2
      - (5 * (m : ℤ) + 13) * ((m : ℤ) + 2) * (PV (m + 2)).2
      - 2 * (2 * (m : ℤ) + 5) * (3 * (m : ℤ) + 4) * (PV (m + 1)).2
      + 4 * (2 * (m : ℤ) + 5) * (2 * (m : ℤ) + 3) * (PV m).2 = 0 := by
  have h3 := PV_succ (m + 2)
  have h2 := PV_succ (m + 1)
  have h1 := PV_succ m
  have hf := f_rec (m + 1)
  have hc3 := cb_step (m + 2)
  have hc2 := cb_step (m + 1)
  push_cast at hc3 hc2
  linear_combination ((m : ℤ) + 3) * ((m : ℤ) + 2) * h3
    - 2 * (2 * (m : ℤ) + 5) * ((m : ℤ) + 2) * h2
    - 4 * (2 * (m : ℤ) + 5) * (2 * (m : ℤ) + 3) * h1
    + ((m : ℤ) + 2) * (fu (m + 2 + 1)).2 * hc3
    + 2 * (2 * (m : ℤ) + 5) * (fu (m + 1)).2 * hc2
    + 2 * (2 * (m : ℤ) + 5) * ((m : ℤ) + 2) * ((m + 1 + 1).centralBinom : ℤ) * hf

end A192251

theorem OMA.solution : type_of% @OMA.S_oeis_a192251.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e1 : m + 4 - 1 = m + 2 + 1 := by omega
  have e2 : m + 4 - 2 = m + 1 + 1 := by omega
  have e3 : m + 4 - 3 = m + 1 := by omega
  rw [e1, e2, e3, show m + 4 = m + 3 + 1 by omega, A192251.a_eq, A192251.a_eq, A192251.a_eq,
    A192251.a_eq]
  have h := A192251.key m
  push_cast
  linear_combination h
