import OMAStatements.S_oeis_a064092
import Mathlib

namespace A064092Aux

def B (p m : ℕ) : ℚ := (((p : ℚ) + 1) - m) * ((p + m).choose m : ℚ) / ((p : ℚ) + 1)

open OMA.S_oeis_a064092 in
lemma a_succ (p : ℕ) : a (p + 1) = ∑ m ∈ Finset.range (p + 1), B p m * 9 ^ m := by
  unfold a B
  rw [if_neg (by omega), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  rw [show p + 1 - 1 + m = p + m from by omega]
  push_cast
  ring

lemma B_zero (p : ℕ) : B p 0 = 1 := by
  unfold B
  have h : ((p : ℚ) + 1) ≠ 0 := by positivity
  rw [Nat.choose_zero_right]
  push_cast
  field_simp
  ring

lemma B_top (p : ℕ) : B p (p + 1) = 0 := by
  unfold B
  push_cast
  ring

lemma B_diag (p : ℕ) : B p p = (catalan p : ℚ) := by
  unfold B
  have h := succ_mul_catalan_eq_centralBinom p
  have h' : ((p : ℚ) + 1) * (catalan p : ℚ) = ((p + p).choose p : ℚ) := by
    have e : (p + 1) * catalan p = (p + p).choose p := by
      rw [h, Nat.centralBinom, two_mul]
    exact_mod_cast e
  have hp : ((p : ℚ) + 1) ≠ 0 := by positivity
  rw [← h']
  field_simp
  ring

lemma B_step (p m : ℕ) : B (p + 1) (m + 1) - B (p + 1) m = B p (m + 1) := by
  unfold B
  have hXY : ((m : ℚ) + 1) * ((p + (m + 1)).choose (m + 1) : ℚ) =
      ((p : ℚ) + 1) * ((p + (m + 1)).choose m : ℚ) := by
    have h := Nat.choose_succ_right_eq (p + (m + 1)) m
    have h2 : p + (m + 1) - m = p + 1 := by omega
    rw [h2] at h
    have e : (((p + (m + 1)).choose (m + 1) * (m + 1) : ℕ) : ℚ) =
        (((p + (m + 1)).choose m * (p + 1) : ℕ) : ℚ) := by rw [h]
    push_cast at e
    linarith
  have hP : ((p + 1 + (m + 1)).choose (m + 1) : ℚ) =
      ((p + (m + 1)).choose (m + 1) : ℚ) + ((p + (m + 1)).choose m : ℚ) := by
    have e : (p + 1 + (m + 1)).choose (m + 1) = (p + (m + 1)).choose m + (p + (m + 1)).choose (m + 1) := by
      rw [show p + 1 + (m + 1) = (p + (m + 1)) + 1 from by ring, Nat.choose_succ_succ]
    rw [e]
    push_cast
    ring
  have hQ : ((p + 1 + m).choose m : ℚ) = ((p + (m + 1)).choose m : ℚ) := by
    rw [show p + 1 + m = p + (m + 1) from by ring]
  rw [hP, hQ]
  have h1 : ((p : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((p : ℚ) + 1 + 1) ≠ 0 := by positivity
  push_cast
  rw [← sub_div, div_eq_div_iff h2 h1]
  linear_combination hXY

open OMA.S_oeis_a064092 in
lemma R_succ (p : ℕ) :
    8 * a (p + 1 + 1) + a (p + 1) = 9 ^ (p + 1 + 1) * (catalan (p + 1) : ℚ) := by
  rw [a_succ (p + 1), a_succ p]
  have e : ∑ m ∈ Finset.range (p + 1), B p m * 9 ^ m =
      ∑ m ∈ Finset.range (p + 1 + 1), B p m * 9 ^ m := by
    rw [Finset.sum_range_succ (fun m => B p m * 9 ^ m) (p + 1), B_top]
    ring
  rw [e, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_range_succ']
  have key : ∀ m ∈ Finset.range (p + 1),
      8 * (B (p + 1) (m + 1) * 9 ^ (m + 1)) + B p (m + 1) * 9 ^ (m + 1) =
        B (p + 1) (m + 1) * 9 ^ (m + 1 + 1) - B (p + 1) m * 9 ^ (m + 1) := by
    intro m _
    rw [← B_step p m]
    ring
  have t := Finset.sum_range_sub (fun m => B (p + 1) m * (9 : ℚ) ^ (m + 1)) (p + 1)
  rw [Finset.sum_congr rfl key, t, B_zero, B_zero, B_diag]
  ring

lemma cat_rec (k : ℕ) :
    ((k : ℚ) + 2) * (catalan (k + 1) : ℚ) = 2 * (2 * (k : ℚ) + 1) * (catalan k : ℚ) := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  have h1' : ((k : ℚ) + 1 + 1) * (catalan (k + 1) : ℚ) = ((k + 1).centralBinom : ℚ) := by
    exact_mod_cast h1
  have h2' : ((k : ℚ) + 1) * (catalan k : ℚ) = (k.centralBinom : ℚ) := by exact_mod_cast h2
  have h3' : ((k : ℚ) + 1) * ((k + 1).centralBinom : ℚ) =
      2 * (2 * (k : ℚ) + 1) * (k.centralBinom : ℚ) := by exact_mod_cast h3
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hk
  linear_combination h3' + ((k : ℚ) + 1) * h1' - 2 * (2 * (k : ℚ) + 1) * h2'

open OMA.S_oeis_a064092 in
lemma R_all (p : ℕ) : 8 * a (p + 1) + a p = 9 ^ (p + 1) * (catalan p : ℚ) := by
  rcases p with _ | q
  · have h0 : a 0 = 1 := by simp [a]
    have h1 : a 1 = 1 := by simp [a]
    rw [h0, h1]
    simp
    norm_num
  · exact R_succ q

end A064092Aux

open OMA.S_oeis_a064092 A064092Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a064092.main := by
  intro n hn
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
  rw [show p + 2 - 1 = p + 1 from by omega, show p + 2 - 2 = p from by omega]
  have r2 : 8 * a (p + 2) + a (p + 1) = 9 ^ (p + 2) * (catalan (p + 1) : ℚ) := R_succ p
  have r1 : 8 * a (p + 1) + a p = 9 ^ (p + 1) * (catalan p : ℚ) := R_all p
  have hc := cat_rec p
  push_cast
  linear_combination ((p : ℚ) + 2) * r2 - 18 * (2 * (p : ℚ) + 1) * r1 + (9 : ℚ) ^ (p + 2) * hc
