import OMAStatements.S_oeis_a079491
import Mathlib

namespace A079491Aux

lemma c2s (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_two_right, Nat.choose_two_right, Nat.triangle_succ]

lemma ch2 (k j : ℕ) : (k + j).choose 2 = k.choose 2 + k * j + j.choose 2 := by
  induction j with
  | zero => simp
  | succ m ih =>
    rw [show k + (m + 1) = (k + m) + 1 by ring, c2s, c2s, ih]
    ring

lemma key (n k : ℕ) (hk : k ≤ n) :
    k * (k - 1) / 2 + ((n - k) * k + (n - k).choose 2) = n * (n - 1) / 2 := by
  have h := ch2 k (n - k)
  rw [show k + (n - k) = n by omega] at h
  rw [← Nat.choose_two_right, ← Nat.choose_two_right, h]
  ring

/-- the claimed numerator -/
def T (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * 2 ^ (k * (n - k) + k.choose 2)

open OMA.S_oeis_a079491 in
lemma ratSum_eq (n : ℕ) : ratSum n = (T n : ℚ) / 2 ^ (n * (n - 1) / 2) := by
  unfold ratSum T
  push_cast
  rw [Finset.sum_div]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [show n + 1 - 1 - k = n - k by omega, show n - (n - k) = k by omega, Nat.choose_symm hk',
    ← key n k hk', pow_add]
  field_simp
  ring

lemma T_odd (n : ℕ) (hn : 2 ≤ n) : Odd (T n) := by
  unfold T
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, zero_mul, zero_add, Nat.choose_zero_succ, pow_zero, mul_one]
  apply Even.add_one
  rw [even_iff_two_dvd]
  refine Finset.dvd_sum (fun k hk => ?_)
  have hk' := Finset.mem_range.mp hk
  have he : (k + 1) * (n - (k + 1)) + (k + 1).choose 2 ≠ 0 := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      have : 1 ≤ (0 + 1) * (n - (0 + 1)) := by omega
      omega
    · have : 0 < (k + 1).choose 2 := Nat.choose_pos (by omega)
      omega
  exact Dvd.dvd.mul_left (dvd_pow_self 2 he) _

end A079491Aux

open OMA.S_oeis_a079491 A079491Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a079491.main := by
  intro n
  show (ratSum n).num = ((T n : ℕ) : ℤ)
  rw [ratSum_eq]
  have hc : Nat.Coprime ((T n : ℤ)).natAbs (((2 ^ (n * (n - 1) / 2) : ℕ) : ℤ)).natAbs := by
    rw [Int.natAbs_natCast, Int.natAbs_natCast]
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · have hM : n * (n - 1) / 2 = 0 := by interval_cases n <;> rfl
      rw [hM, pow_zero]
      exact Nat.coprime_one_right _
    · exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (T_odd n hge))
  have h := Rat.num_div_eq_of_coprime (a := (T n : ℤ)) (b := ((2 ^ (n * (n - 1) / 2) : ℕ) : ℤ))
    (by positivity) hc
  rw [← h]
  push_cast
  rfl
