import OMAStatements.S_oeis_a348618
import Mathlib

namespace A348618
open OMA.S_oeis_a348618

lemma a_even (j : ℕ) :
    a (2 * j + 2) = 4 ^ (2 * j + 2) * ((3 * j + 2).choose (2 * j + 2) : ℚ) := by
  unfold a
  have hpow : (-1 : ℚ) ^ (2 * j + 2) = 1 := Even.neg_one_pow ⟨j + 1, by ring⟩
  rw [hpow, show 3 * (2 * j + 2) / 2 - 1 = 3 * j + 2 by omega]
  ring

lemma a_odd (j : ℕ) :
    a (2 * j + 1) = ((3 * j + 1).choose (2 * j + 1) : ℚ) * ((6 * j + 2).choose (3 * j + 1) : ℚ) /
      ((2 * j).choose j : ℚ) := by
  unfold a
  have hpow : (-1 : ℚ) ^ (2 * j + 1) = -1 := Odd.neg_one_pow ⟨j, by ring⟩
  rw [hpow, show (3 * (2 * j + 1) - 1) / 2 = 3 * j + 1 by omega,
    show 3 * (2 * j + 1) - 1 = 6 * j + 2 by omega, show 2 * j + 1 - 1 = 2 * j by omega,
    show 2 * j / 2 = j by omega]
  ring

lemma E1 (j : ℕ) :
    (2 * (j : ℚ) + 4) * (2 * (j : ℚ) + 3) * ((3 * j + 5).choose (2 * j + 4) : ℚ) =
      3 * (3 * (j : ℚ) + 5) * (3 * (j : ℚ) + 4) * ((3 * j + 2).choose (2 * j + 2) : ℚ) := by
  have h1 : ((3 * j + 5).choose (2 * j + 4) : ℚ) =
      ((3 * j + 5).factorial : ℚ) / ((2 * j + 4).factorial * (j + 1).factorial) := by
    have h := Nat.cast_add_choose ℚ (a := 2 * j + 4) (b := j + 1)
    rw [show 2 * j + 4 + (j + 1) = 3 * j + 5 by ring] at h
    exact h
  have h2 : ((3 * j + 2).choose (2 * j + 2) : ℚ) =
      ((3 * j + 2).factorial : ℚ) / ((2 * j + 2).factorial * j.factorial) := by
    have h := Nat.cast_add_choose ℚ (a := 2 * j + 2) (b := j)
    rw [show 2 * j + 2 + j = 3 * j + 2 by ring] at h
    exact h
  have f1 : ((3 * j + 5).factorial : ℚ) =
      (3 * (j : ℚ) + 5) * (3 * (j : ℚ) + 4) * (3 * (j : ℚ) + 3) * ((3 * j + 2).factorial : ℚ) := by
    rw [show 3 * j + 5 = (3 * j + 2) + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    ring
  have f2 : ((2 * j + 4).factorial : ℚ) =
      (2 * (j : ℚ) + 4) * (2 * (j : ℚ) + 3) * ((2 * j + 2).factorial : ℚ) := by
    rw [show 2 * j + 4 = (2 * j + 2) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f3 : ((j + 1).factorial : ℚ) = ((j : ℚ) + 1) * (j.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have p1 : ((3 * j + 2).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have p2 : ((2 * j + 2).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have p3 : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have q1 : (2 * (j : ℚ) + 4) ≠ 0 := by positivity
  have q2 : (2 * (j : ℚ) + 3) ≠ 0 := by positivity
  have q3 : ((j : ℚ) + 1) ≠ 0 := by positivity
  rw [h1, h2, f1, f2, f3]
  field_simp

lemma O1 (j : ℕ) :
    (2 * (j : ℚ) + 3) * (2 * (j : ℚ) + 2) * ((3 * j + 4).choose (2 * j + 3) : ℚ) =
      3 * (3 * (j : ℚ) + 4) * (3 * (j : ℚ) + 2) * ((3 * j + 1).choose (2 * j + 1) : ℚ) := by
  have h1 : ((3 * j + 4).choose (2 * j + 3) : ℚ) =
      ((3 * j + 4).factorial : ℚ) / ((2 * j + 3).factorial * (j + 1).factorial) := by
    have h := Nat.cast_add_choose ℚ (a := 2 * j + 3) (b := j + 1)
    rw [show 2 * j + 3 + (j + 1) = 3 * j + 4 by ring] at h
    exact h
  have h2 : ((3 * j + 1).choose (2 * j + 1) : ℚ) =
      ((3 * j + 1).factorial : ℚ) / ((2 * j + 1).factorial * j.factorial) := by
    have h := Nat.cast_add_choose ℚ (a := 2 * j + 1) (b := j)
    rw [show 2 * j + 1 + j = 3 * j + 1 by ring] at h
    exact h
  have f1 : ((3 * j + 4).factorial : ℚ) =
      (3 * (j : ℚ) + 4) * (3 * (j : ℚ) + 3) * (3 * (j : ℚ) + 2) * ((3 * j + 1).factorial : ℚ) := by
    rw [show 3 * j + 4 = (3 * j + 1) + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    ring
  have f2 : ((2 * j + 3).factorial : ℚ) =
      (2 * (j : ℚ) + 3) * (2 * (j : ℚ) + 2) * ((2 * j + 1).factorial : ℚ) := by
    rw [show 2 * j + 3 = (2 * j + 1) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f3 : ((j + 1).factorial : ℚ) = ((j : ℚ) + 1) * (j.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have p1 : ((3 * j + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have p2 : ((2 * j + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have p3 : (j.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have q1 : (2 * (j : ℚ) + 3) ≠ 0 := by positivity
  have q2 : (2 * (j : ℚ) + 2) ≠ 0 := by positivity
  have q3 : ((j : ℚ) + 1) ≠ 0 := by positivity
  rw [h1, h2, f1, f2, f3]
  field_simp

lemma cb_step (k : ℕ) :
    ((k : ℚ) + 1) * ((k + 1).centralBinom : ℚ) = 2 * (2 * (k : ℚ) + 1) * (k.centralBinom : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ k
  have h' : (((k + 1) * (k + 1).centralBinom : ℕ) : ℚ) = ((2 * (2 * k + 1) * k.centralBinom : ℕ) : ℚ) := by
    rw [h]
  push_cast at h'
  exact h'

lemma cb_eq (k : ℕ) : (2 * k).choose k = k.centralBinom := (Nat.centralBinom_eq_two_mul_choose k).symm

lemma O2 (j : ℕ) :
    (3 * (j : ℚ) + 4) * (3 * (j : ℚ) + 3) * (3 * (j : ℚ) + 2) * ((6 * j + 8).choose (3 * j + 4) : ℚ) =
      8 * (6 * (j : ℚ) + 7) * (6 * (j : ℚ) + 5) * (6 * (j : ℚ) + 3) *
        ((6 * j + 2).choose (3 * j + 1) : ℚ) := by
  rw [show 6 * j + 8 = 2 * (3 * j + 4) by ring, show 6 * j + 2 = 2 * (3 * j + 1) by ring,
    cb_eq, cb_eq]
  have s3 := cb_step (3 * j + 3)
  have s2 := cb_step (3 * j + 2)
  have s1 := cb_step (3 * j + 1)
  rw [show 3 * j + 3 + 1 = 3 * j + 4 by ring] at s3
  rw [show 3 * j + 2 + 1 = 3 * j + 3 by ring] at s2
  rw [show 3 * j + 1 + 1 = 3 * j + 2 by ring] at s1
  push_cast at s1 s2 s3
  linear_combination (3 * (j : ℚ) + 3) * (3 * (j : ℚ) + 2) * s3
    + 2 * (6 * (j : ℚ) + 7) * (3 * (j : ℚ) + 2) * s2
    + 4 * (6 * (j : ℚ) + 7) * (6 * (j : ℚ) + 5) * s1

lemma O3 (j : ℕ) :
    ((j : ℚ) + 1) * ((2 * j + 2).choose (j + 1) : ℚ) = 2 * (2 * (j : ℚ) + 1) * ((2 * j).choose j : ℚ) := by
  rw [show 2 * j + 2 = 2 * (j + 1) by ring, cb_eq, cb_eq]
  exact cb_step j

lemma odd_rec (j : ℕ) :
    (2 * (j : ℚ) + 3) * (2 * (j : ℚ) + 2) * a (2 * j + 3) =
      12 * (6 * (j : ℚ) + 7) * (6 * (j : ℚ) + 5) * a (2 * j + 1) := by
  rw [show 2 * j + 3 = 2 * (j + 1) + 1 by ring, a_odd (j + 1), a_odd j,
    show 3 * (j + 1) + 1 = 3 * j + 4 by ring, show 2 * (j + 1) + 1 = 2 * j + 3 by ring,
    show 6 * (j + 1) + 2 = 6 * j + 8 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
  have h1 := O1 j
  have h2 := O2 j
  have h3 := O3 j
  have hY3 : ((2 * j).choose j : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hX3 : ((2 * j + 2).choose (j + 1) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have q1 : (2 * (j : ℚ) + 3) ≠ 0 := by positivity
  have q2 : (2 * (j : ℚ) + 2) ≠ 0 := by positivity
  have q3 : ((j : ℚ) + 1) ≠ 0 := by positivity
  have q4 : (3 * (j : ℚ) + 4) ≠ 0 := by positivity
  have q5 : (3 * (j : ℚ) + 3) ≠ 0 := by positivity
  have q6 : (3 * (j : ℚ) + 2) ≠ 0 := by positivity
  have e1 : ((3 * j + 4).choose (2 * j + 3) : ℚ) =
      3 * (3 * (j : ℚ) + 4) * (3 * (j : ℚ) + 2) * ((3 * j + 1).choose (2 * j + 1) : ℚ) /
        ((2 * (j : ℚ) + 3) * (2 * (j : ℚ) + 2)) := by
    rw [eq_div_iff (mul_ne_zero q1 q2)]
    linear_combination h1
  have e2 : ((6 * j + 8).choose (3 * j + 4) : ℚ) =
      8 * (6 * (j : ℚ) + 7) * (6 * (j : ℚ) + 5) * (6 * (j : ℚ) + 3) *
        ((6 * j + 2).choose (3 * j + 1) : ℚ) /
        ((3 * (j : ℚ) + 4) * (3 * (j : ℚ) + 3) * (3 * (j : ℚ) + 2)) := by
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero q4 q5) q6)]
    linear_combination h2
  have e3 : ((2 * j + 2).choose (j + 1) : ℚ) =
      2 * (2 * (j : ℚ) + 1) * ((2 * j).choose j : ℚ) / ((j : ℚ) + 1) := by
    rw [eq_div_iff q3]
    linear_combination h3
  have q7 : (2 * (j : ℚ) + 1) ≠ 0 := by positivity
  rw [e1, e2, e3]
  field_simp
  ring

end A348618

theorem OMA.solution : type_of% @OMA.S_oeis_a348618.main := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [show 2 * (j + 2) - 2 = 2 * j + 2 by omega, show 2 * (j + 2) = 2 * (j + 1) + 2 by ring,
      A348618.a_even (j + 1), A348618.a_even j,
      show 3 * (j + 1) + 2 = 3 * j + 5 by ring, show 2 * (j + 1) + 2 = 2 * j + 4 by ring]
    have h := A348618.E1 j
    push_cast
    linear_combination (4 : ℚ) ^ (2 * j + 4) * h
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) + 1 - 2 = 2 * j + 1 by omega, show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
    have h := A348618.odd_rec j
    push_cast
    linear_combination h
