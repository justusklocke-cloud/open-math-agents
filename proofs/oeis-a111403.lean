import OMAStatements.S_oeis_a111403
import Mathlib

namespace A111403

open OMA.S_oeis_a111403 in
lemma even_step (k : ℕ) :
    A002716 (2 * k + 2) = A002716 (2 * k + 1) ^ 2 - 3 * A002716 (2 * k + 1) + 3 := by
  rw [A002716, if_pos (by omega)]

open OMA.S_oeis_a111403 in
lemma odd_step (k : ℕ) :
    A002716 (2 * k + 1 + 2) = A002716 (2 * k + 2) + A002716 (2 * k + 1) - 1 := by
  rw [A002716, if_neg (by omega)]

open OMA.S_oeis_a111403 in
lemma odd_value (n : ℕ) : A002716 (2 * n + 1) = 2 ^ (2 ^ (n + 1)) + 1 := by
  induction n with
  | zero => simp [A002716]
  | succ k ih =>
    have e : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
    rw [e, odd_step, even_step, ih]
    have : (2 : ℤ) ^ (2 ^ (k + 1 + 1)) = (2 ^ (2 ^ (k + 1))) ^ 2 := by
      rw [← pow_mul, pow_succ 2 (k + 1)]
    rw [this]; ring

end A111403

theorem OMA.solution : type_of% @OMA.S_oeis_a111403.main := by
  intro n
  unfold OMA.S_oeis_a111403.a OMA.S_oeis_a111403.f
  rcases n with _ | k
  · simp [OMA.S_oeis_a111403.A002716]
  · have e : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [e, A111403.even_step, A111403.odd_value]
    have : (2 : ℤ) ^ (2 ^ (k + 1 + 1)) = (2 ^ (2 ^ (k + 1))) ^ 2 := by
      rw [← pow_mul, pow_succ 2 (k + 1)]
    push_cast
    rw [this]; ring
