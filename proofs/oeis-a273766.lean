import OMAStatements.S_oeis_a273766
import Mathlib

namespace A273766Aux

open OMA.S_oeis_a273766 in
def off (L : List (ℤ × ℤ)) : Grid := fun x y => !decide ((x, y) ∈ L)

def inBox (L : List (ℤ × ℤ)) : Prop := ∀ p ∈ L, -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1

lemma off_far (L : List (ℤ × ℤ)) (hL : inBox L) (u v : ℤ)
    (h : ¬(-1 ≤ u ∧ u ≤ 1 ∧ -1 ≤ v ∧ v ≤ 1)) : off L u v = true := by
  unfold off
  have hm : (u, v) ∉ L := fun hm => h (hL _ hm)
  simp [hm]

def five : List ℤ := [-2, -1, 0, 1, 2]

lemma mem_five (x : ℤ) (h1 : -2 ≤ x) (h2 : x ≤ 2) : x ∈ five := by
  unfold five
  simp
  omega

open OMA.S_oeis_a273766 in
lemma step_off (L L' : List (ℤ × ℤ)) (hL : inBox L) (hL' : inBox L')
    (hbox : ∀ x ∈ five, ∀ y ∈ five, step (off L) x y = off L' x y) :
    step (off L) = off L' := by
  funext x y
  by_cases h : (-2 ≤ x ∧ x ≤ 2) ∧ (-2 ≤ y ∧ y ≤ 2)
  · exact hbox x (mem_five x h.1.1 h.1.2) y (mem_five y h.2.1 h.2.2)
  · rw [off_far L' hL' x y (by omega)]
    unfold step neighbors
    rw [off_far L hL x y (by omega), off_far L hL (x + 1) y (by omega),
      off_far L hL (x - 1) y (by omega), off_far L hL x (y + 1) (by omega),
      off_far L hL x (y - 1) (by omega)]
    decide

open OMA.S_oeis_a273766 in
lemma initial_far (u v : ℤ) (h : ¬(u = 0 ∧ v = 0)) : initial u v = false := by
  unfold initial
  simp only [decide_eq_false_iff_not]
  exact h

open OMA.S_oeis_a273766 in
lemma step_initial (L' : List (ℤ × ℤ)) (hL' : inBox L')
    (hbox : ∀ x ∈ five, ∀ y ∈ five, step initial x y = off L' x y) :
    step initial = off L' := by
  funext x y
  by_cases h : (-2 ≤ x ∧ x ≤ 2) ∧ (-2 ≤ y ∧ y ≤ 2)
  · exact hbox x (mem_five x h.1.1 h.1.2) y (mem_five y h.2.1 h.2.2)
  · rw [off_far L' hL' x y (by omega)]
    unfold step neighbors
    rw [initial_far x y (by omega), initial_far (x + 1) y (by omega),
      initial_far (x - 1) y (by omega), initial_far x (y + 1) (by omega),
      initial_far x (y - 1) (by omega)]
    decide

open OMA.S_oeis_a273766 in
lemma s1 : state 1 = off [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] :=
  step_initial _ (by unfold inBox; decide) (by decide)

open OMA.S_oeis_a273766 in
lemma s2 : state 2 = off [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)] := by
  show step (state 1) = _
  rw [s1]
  exact step_off _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide)

open OMA.S_oeis_a273766 in
lemma s3 : state 3 = off [(0, 0)] := by
  show step (state 2) = _
  rw [s2]
  exact step_off _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide)

open OMA.S_oeis_a273766 in
lemma s4 : state 4 = off [] := by
  show step (state 3) = _
  rw [s3]
  exact step_off _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide)

open OMA.S_oeis_a273766 in
lemma sN (n : ℕ) : state (n + 4) = off [] := by
  induction n with
  | zero => exact s4
  | succ k ih =>
    show step (state (k + 4)) = _
    rw [ih]
    exact step_off _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide)

open OMA.S_oeis_a273766 in
lemma a_big (n : ℕ) : a (n + 4) = (2 * (n + 4) + 1) ^ 2 := by
  have h : ∀ u v : ℤ, bit (off [] u v) = 1 := by
    intro u v
    simp [off, bit]
  unfold a
  rw [sN]
  simp only [h, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  ring

open OMA.S_oeis_a273766 in
lemma a_cl (n : ℕ) (hn : 4 ≤ n) : (a n : ℤ) = (2 * (n : ℤ) + 1) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [a_big]
  push_cast
  ring

open OMA.S_oeis_a273766 in
lemma a0 : a 0 = 1 := by decide

open OMA.S_oeis_a273766 in
lemma a1 : a 1 = 4 := by
  unfold a
  rw [s1]
  decide

open OMA.S_oeis_a273766 in
lemma a2 : a 2 = 17 := by
  unfold a
  rw [s2]
  decide

open OMA.S_oeis_a273766 in
lemma a3 : a 3 = 48 := by
  unfold a
  rw [s3]
  decide

open PowerSeries in
lemma coeff_term (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A273766Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a273766 A273766Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a273766.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [a_big]; ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
    simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega]
    rw [a_cl (m + 7) (by omega), a_cl (m + 6) (by omega), a_cl (m + 5) (by omega),
      a_cl (m + 4) (by omega)]
    push_cast
    ring
  · have hD : ((1 : PowerSeries ℤ) - PowerSeries.X) ^ 3 =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-3) * PowerSeries.X ^ 1 +
        PowerSeries.C 3 * PowerSeries.X ^ 2 + PowerSeries.C (-1) * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + PowerSeries.X + 8 * PowerSeries.X ^ 2 + 8 * PowerSeries.X ^ 3
        - 16 * PowerSeries.X ^ 4 + 5 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6 : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 1 * PowerSeries.X ^ 1 +
        PowerSeries.C 8 * PowerSeries.X ^ 2 + PowerSeries.C 8 * PowerSeries.X ^ 3 +
        PowerSeries.C (-16) * PowerSeries.X ^ 4 + PowerSeries.C 5 * PowerSeries.X ^ 5 +
        PowerSeries.C 1 * PowerSeries.X ^ 6 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    have e4 := a_cl 4 (by omega)
    have e5 := a_cl 5 (by omega)
    have e6 := a_cl 6 (by omega)
    rcases n with _ | _ | _ | _ | _ | _ | _ | n
    · simp [a0]
    · simp [a0, a1]
    · simp [a0, a1, a2]
    · simp [a0, a1, a2, a3]
    · simp [a1, a2, a3, e4]
    · simp [a2, a3, e4, e5]
    · simp [a3, e4, e5, e6]
    · have f7 := a_cl (n + 7) (by omega)
      have f6 := a_cl (n + 6) (by omega)
      have f5 := a_cl (n + 5) (by omega)
      have f4 := a_cl (n + 4) (by omega)
      simp [f7, f6, f5, f4]
      ring
