import OMAStatements.S_oeis_a130770
import Mathlib

namespace A130770

lemma caseA (k : ℕ) :
    ((((3 * k + 1 : ℕ) : ℚ) - 1) ^ 2 / (((3 * k + 1 : ℕ) : ℚ) ^ 2 + ((3 * k + 1 : ℕ) : ℚ) + 1)).den
      = 3 * k ^ 2 + 3 * k + 1 := by
  have hpos : (0 : ℚ) < 3 * (k : ℚ) ^ 2 + 3 * k + 1 := by positivity
  have e : (((3 * k + 1 : ℕ) : ℚ) - 1) ^ 2 / (((3 * k + 1 : ℕ) : ℚ) ^ 2 + ((3 * k + 1 : ℕ) : ℚ) + 1)
      = ((3 * (k : ℤ) ^ 2 : ℤ) : ℚ) / ((3 * (k : ℤ) ^ 2 + 3 * k + 1 : ℤ) : ℚ) := by
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [e]
  have hcop : Nat.Coprime (3 * (k : ℤ) ^ 2).natAbs (3 * (k : ℤ) ^ 2 + 3 * k + 1).natAbs := by
    have hg : Int.gcd (3 * (k : ℤ) ^ 2) (3 * (k : ℤ) ^ 2 + 3 * k + 1) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp ⟨3 * k + 2, -(3 * k - 1), by ring⟩
    exact hg
  have h := Rat.den_div_eq_of_coprime (a := 3 * (k : ℤ) ^ 2) (b := 3 * (k : ℤ) ^ 2 + 3 * k + 1)
    (by positivity) hcop
  exact_mod_cast h

lemma caseB (m : ℕ) (h3 : ¬ 3 ∣ m) :
    ((((m + 1 : ℕ) : ℚ) - 1) ^ 2 / (((m + 1 : ℕ) : ℚ) ^ 2 + ((m + 1 : ℕ) : ℚ) + 1)).den
      = m ^ 2 + 3 * m + 3 := by
  have e : (((m + 1 : ℕ) : ℚ) - 1) ^ 2 / (((m + 1 : ℕ) : ℚ) ^ 2 + ((m + 1 : ℕ) : ℚ) + 1)
      = (((m : ℤ) ^ 2 : ℤ) : ℚ) / (((m : ℤ) ^ 2 + 3 * m + 3 : ℤ) : ℚ) := by
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [e]
  have hc1 : Nat.Coprime m (m ^ 2 + 3 * m + 3) := by
    have h : m ^ 2 + 3 * m + 3 = m * (m + 3) + 3 := by ring
    rw [h, Nat.coprime_mul_left_add_right]
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
  have hcop : Nat.Coprime ((m : ℤ) ^ 2).natAbs ((m : ℤ) ^ 2 + 3 * m + 3).natAbs := by
    have e1 : ((m : ℤ) ^ 2).natAbs = m ^ 2 := by
      rw [Int.natAbs_pow, Int.natAbs_natCast]
    have e2 : ((m : ℤ) ^ 2 + 3 * m + 3).natAbs = m ^ 2 + 3 * m + 3 := by
      have : ((m : ℤ) ^ 2 + 3 * m + 3) = ((m ^ 2 + 3 * m + 3 : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.natAbs_natCast]
    rw [e1, e2]
    exact Nat.Coprime.pow_left 2 hc1
  have h := Rat.den_div_eq_of_coprime (a := (m : ℤ) ^ 2) (b := (m : ℤ) ^ 2 + 3 * m + 3)
    (by positivity) hcop
  exact_mod_cast h

end A130770

theorem OMA.solution : type_of% @OMA.S_oeis_a130770.main := by
  intro n hn
  unfold OMA.S_oeis_a130770.a OMA.S_oeis_a130770.A046163
  by_cases h : n % 3 = 1
  · obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 1 := ⟨n / 3, by omega⟩
    rw [A130770.caseA]
    have e : (3 * k + 1) ^ 2 + (3 * k + 1) + 1 = 3 * (3 * k ^ 2 + 3 * k + 1) := by ring
    rw [e, Nat.lcm_eq_right (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (by norm_num)]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h3 : ¬ 3 ∣ m := by omega
    rw [A130770.caseB m h3]
    have e : (m + 1) ^ 2 + (m + 1) + 1 = m ^ 2 + 3 * m + 3 := by ring
    rw [e]
    have hc : Nat.Coprime 3 (m ^ 2 + 3 * m + 3) := by
      have h' : m ^ 2 + 3 * m + 3 = 3 * (m + 1) + m ^ 2 := by ring
      rw [h', Nat.coprime_mul_left_add_right]
      exact Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    rw [hc.lcm_eq_mul, Nat.mul_div_cancel_left _ (by norm_num)]
