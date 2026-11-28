import OMAStatements.S_oeis_a237930
import Mathlib

namespace A237930

lemma two_a (n : ℕ) : 2 * OMA.S_oeis_a237930.a n + 1 = 7 * 3 ^ n := by
  unfold OMA.S_oeis_a237930.a
  have hodd : Odd (3 ^ n) := Odd.pow (by decide)
  obtain ⟨k, hk⟩ := hodd
  have : 3 ^ (n + 1) = 3 * 3 ^ n := by ring
  omega

/-- If 3 is a square and 7 is not, then `7 * 3 ^ n ≠ 1`. -/
lemma no_sol {p : ℕ} [Fact p.Prime] (h3 : IsSquare (3 : ZMod p)) (h7 : ¬ IsSquare (7 : ZMod p))
    (n : ℕ) : (7 : ZMod p) * 3 ^ n ≠ 1 := by
  intro h
  obtain ⟨x, hx⟩ := h3
  apply h7
  have hx0 : x ^ n ≠ 0 := by
    intro h0
    rw [hx, ← pow_two, ← pow_mul, mul_comm 2 n, pow_mul, h0] at h
    simp at h
  refine ⟨(x ^ n)⁻¹, ?_⟩
  rw [hx, ← pow_two, ← pow_mul, mul_comm 2 n, pow_mul, pow_two] at h
  field_simp
  linear_combination h

lemma s3_one : IsSquare ((1 : ℕ) : ZMod 3) := by decide
lemma s3_two : ¬ IsSquare ((2 : ℕ) : ZMod 3) := by decide
lemma s7_one : IsSquare ((1 : ℕ) : ZMod 7) := by decide
lemma s7_two : IsSquare ((2 : ℕ) : ZMod 7) := by decide
lemma s7_four : IsSquare ((4 : ℕ) : ZMod 7) := by decide
lemma s7_three : ¬ IsSquare ((3 : ℕ) : ZMod 7) := by decide
lemma s7_five : ¬ IsSquare ((5 : ℕ) : ZMod 7) := by decide
lemma s7_six : ¬ IsSquare ((6 : ℕ) : ZMod 7) := by decide

end A237930

theorem OMA.solution : type_of% @OMA.S_oeis_a237930.main := by
  intro n p hp hdvd hmem
  have hfp : Fact p.Prime := ⟨hp⟩
  have hz : ((OMA.S_oeis_a237930.a n : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have h1 : (7 : ZMod p) * 3 ^ n = 1 := by
    have h := congrArg (fun t : ℕ => (t : ZMod p)) (A237930.two_a n)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, hz] at h
    rw [← h]; ring
  have hf3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have c3 : ((p : ℕ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod p 3).symm
  have c7 : ((p : ℕ) : ZMod 7) = ((p % 7 : ℕ) : ZMod 7) := (ZMod.natCast_mod p 7).symm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hmod4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases hmod4 with h4 | h4
  · -- p ≡ 13, 61, 73 (mod 84)
    have q3 := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := 3) h4 (by norm_num)
    have q7 := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := 7) h4 (by norm_num)
    have s3 : IsSquare ((3 : ℕ) : ZMod p) := by
      rw [q3, c3]
      have : p % 3 = 1 := by omega
      rw [this]; exact A237930.s3_one
    have s7 : ¬ IsSquare ((7 : ℕ) : ZMod p) := by
      rw [q7, c7]
      have : p % 7 = 6 ∨ p % 7 = 5 ∨ p % 7 = 3 := by omega
      rcases this with h | h | h <;> rw [h]
      · exact A237930.s7_six
      · exact A237930.s7_five
      · exact A237930.s7_three
    exact A237930.no_sol (by exact_mod_cast s3) (by exact_mod_cast s7) n h1
  · -- p ≡ 11, 23, 71 (mod 84)
    have q3 := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := p) (q := 3) h4 (by norm_num)
      (by omega)
    have q7 := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := p) (q := 7) h4 (by norm_num)
      (by omega)
    have s3 : IsSquare ((3 : ℕ) : ZMod p) := by
      rw [q3, c3]
      have : p % 3 = 2 := by omega
      rw [this]; exact A237930.s3_two
    have s7 : ¬ IsSquare ((7 : ℕ) : ZMod p) := by
      rw [q7, c7, not_not]
      have : p % 7 = 4 ∨ p % 7 = 2 ∨ p % 7 = 1 := by omega
      rcases this with h | h | h <;> rw [h]
      · exact A237930.s7_four
      · exact A237930.s7_two
      · exact A237930.s7_one
    exact A237930.no_sol (by exact_mod_cast s3) (by exact_mod_cast s7) n h1
