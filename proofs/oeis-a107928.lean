import OMAStatements.S_oeis_a107928
import Mathlib

namespace A107928
open OMA.S_oeis_a107928

lemma a_step (n : ℕ) :
    a (n + 3) = ((2 * a (n + 2) * a (n + 1) : ℚ) / ((a (n + 1) : ℚ) + a (n + 2))).num := by
  rw [a]

lemma a_one : a 1 = 2 := by rw [a]

lemma a_two : a 2 = 3 := by rw [a]

lemma num_helper (x y N D : ℤ) (hD : 0 < D) (hcop : Nat.Coprime N.natAbs D.natAbs)
    (hx : x + y ≠ 0) (h : 2 * y * x * D = N * (x + y)) :
    ((2 * (y : ℚ) * (x : ℚ)) / ((x : ℚ) + (y : ℚ))).num = N := by
  have hxq : ((x : ℚ) + (y : ℚ)) ≠ 0 := by exact_mod_cast hx
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have e : (2 * (y : ℚ) * (x : ℚ)) / ((x : ℚ) + (y : ℚ)) = (N : ℚ) / (D : ℚ) := by
    rw [div_eq_div_iff hxq hDq]
    exact_mod_cast h
  rw [e]
  exact Rat.num_div_eq_of_coprime hD hcop

lemma cop (c d : ℤ) (k : ℕ) (h1 : Nat.Coprime c.natAbs d.natAbs)
    (h2 : Nat.Coprime (8 : ℤ).natAbs d.natAbs) : Nat.Coprime (c * 8 ^ k).natAbs d.natAbs := by
  rw [Int.natAbs_mul, Int.natAbs_pow]
  exact Nat.Coprime.mul_left h1 (Nat.Coprime.pow_left k h2)

lemma triple (k : ℕ) :
    a (3 * k + 3) = 12 * 8 ^ k ∧ a (3 * k + 4) = 24 * 8 ^ k ∧ a (3 * k + 5) = 16 * 8 ^ k := by
  induction k with
  | zero =>
    have h3 : a 3 = 12 := by
      rw [a_step 0, a_one, a_two]
      exact num_helper 2 3 12 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h4 : a 4 = 24 := by
      rw [a_step 1, h3, a_two]
      exact num_helper 3 12 24 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h5 : a 5 = 16 := by
      rw [a_step 2, h4, h3]
      exact num_helper 12 24 16 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    refine ⟨?_, ?_, ?_⟩
    · simpa using h3
    · simpa using h4
    · simpa using h5
  | succ k ih =>
    obtain ⟨h3, h4, h5⟩ := ih
    have hpos : (0 : ℤ) < 8 ^ k := by positivity
    have g6 : a (3 * k + 6) = 12 * 8 ^ (k + 1) := by
      rw [show 3 * k + 6 = (3 * k + 3) + 3 by omega, a_step,
        show 3 * k + 3 + 2 = 3 * k + 5 by omega, show 3 * k + 3 + 1 = 3 * k + 4 by omega, h5, h4]
      refine num_helper (24 * 8 ^ k) (16 * 8 ^ k) (12 * 8 ^ (k + 1)) 5 (by norm_num)
        (cop 12 5 (k + 1) (by norm_num) (by norm_num)) (by nlinarith) (by ring)
    have g7 : a (3 * k + 7) = 24 * 8 ^ (k + 1) := by
      rw [show 3 * k + 7 = (3 * k + 4) + 3 by omega, a_step,
        show 3 * k + 4 + 2 = 3 * k + 6 by omega, show 3 * k + 4 + 1 = 3 * k + 5 by omega, g6, h5]
      refine num_helper (16 * 8 ^ k) (12 * 8 ^ (k + 1)) (24 * 8 ^ (k + 1)) 7 (by norm_num)
        (cop 24 7 (k + 1) (by norm_num) (by norm_num)) (by nlinarith [pow_succ (8 : ℤ) k]) (by ring)
    have g8 : a (3 * k + 8) = 16 * 8 ^ (k + 1) := by
      rw [show 3 * k + 8 = (3 * k + 5) + 3 by omega, a_step,
        show 3 * k + 5 + 2 = 3 * k + 7 by omega, show 3 * k + 5 + 1 = 3 * k + 6 by omega, g7, g6]
      refine num_helper (12 * 8 ^ (k + 1)) (24 * 8 ^ (k + 1)) (16 * 8 ^ (k + 1)) 1 (by norm_num)
        (by simp) (by nlinarith [pow_succ (8 : ℤ) k]) (by ring)
    refine ⟨?_, ?_, ?_⟩
    · rw [show 3 * (k + 1) + 3 = 3 * k + 6 by omega]; exact g6
    · rw [show 3 * (k + 1) + 4 = 3 * k + 7 by omega]; exact g7
    · rw [show 3 * (k + 1) + 5 = 3 * k + 8 by omega]; exact g8

end A107928

theorem OMA.solution : type_of% @OMA.S_oeis_a107928.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨h3, h4, h5⟩ := A107928.triple k
  refine ⟨?_, ?_, ?_⟩
  · rw [show 3 * (k + 1) = 3 * k + 3 by omega, h3]
    push_cast
    ring
  · rw [show 3 * (k + 1) + 1 = 3 * k + 4 by omega, h4]
    ring
  · rw [show 3 * (k + 1) + 2 = 3 * k + 5 by omega, h5]
    ring
