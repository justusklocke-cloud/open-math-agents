import OMAStatements.S_oeis_a084091
import Mathlib

namespace A084091Aux

def chi (m : ℕ) : ℚ := if m % 3 = 1 then 1 else if m % 3 = 2 then -1 else 0

lemma chi0 (m : ℕ) (h : m % 3 = 0) : chi m = 0 := by
  unfold chi
  have n1 : ¬ (m % 3 = 1) := by omega
  have n2 : ¬ (m % 3 = 2) := by omega
  rw [if_neg n1, if_neg n2]

lemma chi1 (m : ℕ) (h : m % 3 = 1) : chi m = 1 := by
  unfold chi
  rw [if_pos h]

lemma chi2 (m : ℕ) (h : m % 3 = 2) : chi m = -1 := by
  unfold chi
  have n1 : ¬ (m % 3 = 1) := by omega
  rw [if_neg n1, if_pos h]

lemma lt_two_pow (k : ℕ) : k < 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; omega

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

open PowerSeries in
lemma gf : (X * (1 + X + X ^ 2 : PowerSeries ℚ)⁻¹) = mk chi := by
  have hc : constantCoeff (1 + X + X ^ 2 : PowerSeries ℚ) ≠ 0 := by simp
  symm
  rw [PowerSeries.eq_mul_inv_iff_mul_eq hc]
  have hD : (1 + X + X ^ 2 : PowerSeries ℚ) = C 1 * X ^ 0 + C 1 * X ^ 1 + C 1 * X ^ 2 := by
    simp only [map_one]; ring
  rw [hD]
  ext n
  simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_X]
  by_cases h2 : 2 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have c0 : (0 : ℕ) ≤ m + 2 := by omega
    have c1 : (1 : ℕ) ≤ m + 2 := by omega
    have c2 : (2 : ℕ) ≤ m + 2 := by omega
    have n1 : ¬ (m + 2 = 1) := by omega
    have d0 : m + 2 - 0 = m + 2 := by omega
    have d1 : m + 2 - 1 = m + 1 := by omega
    have d2 : m + 2 - 2 = m := by omega
    rw [if_pos c0, if_pos c1, if_pos c2, if_neg n1, d0, d1, d2]
    have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hm with h | h | h
    · rw [chi0 m h, chi1 (m + 1) (by omega), chi2 (m + 2) (by omega)]; norm_num
    · rw [chi1 m h, chi2 (m + 1) (by omega), chi0 (m + 2) (by omega)]; norm_num
    · rw [chi2 m h, chi0 (m + 1) (by omega), chi1 (m + 2) (by omega)]; norm_num
  · have hn : n = 0 ∨ n = 1 := by omega
    rcases hn with rfl | rfl
    · norm_num [chi]
    · norm_num [chi]

lemma reindex (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n + 1), if 2 ^ k ∣ n then chi (n / 2 ^ k) else 0)
      = ∑ d ∈ n.divisors, if (n / d).primeFactors ⊆ {2} then chi d else 0 := by
  have hn0 : n ≠ 0 := by omega
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_bij (fun k _ => n / 2 ^ k)
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨Nat.div_dvd_of_dvd hk.2, hn0⟩, ?_⟩
    rw [Nat.div_div_self hk.2 hn0]
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Finset.mem_singleton]
    exact (Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_two).mp (hp.1.dvd_of_dvd_pow hp.2.1)
  · intro k1 hk1 k2 hk2 h
    rw [Finset.mem_filter, Finset.mem_range] at hk1 hk2
    have h2 : n / 2 ^ k1 = n / 2 ^ k2 := h
    have e1 : n / (n / 2 ^ k1) = 2 ^ k1 := Nat.div_div_self hk1.2 hn0
    have e2 : n / (n / 2 ^ k2) = 2 ^ k2 := Nat.div_div_self hk2.2 hn0
    have h' : (2 : ℕ) ^ k1 = 2 ^ k2 := by
      rw [← e1, ← e2, h2]
    exact Nat.pow_right_injective (le_refl 2) h'
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdn, _⟩, hpf⟩ := hd
    have hq0 : n / d ≠ 0 := by
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
      have hpos := Nat.div_pos (Nat.le_of_dvd (by omega) hdn) hdpos
      omega
    have hq : n / d = 2 ^ (n / d).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hq0 (fun {p} hp hpd => by
        have hmem : p ∈ (n / d).primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hq0⟩
        exact Finset.mem_singleton.mp (hpf hmem))
    have hle : n / d ≤ n := Nat.div_le_self n d
    have hlt := lt_two_pow (n / d).primeFactorsList.length
    have hdvd : 2 ^ (n / d).primeFactorsList.length ∣ n := by
      rw [← hq]
      exact Nat.div_dvd_of_dvd hdn
    have hmemk : (n / d).primeFactorsList.length
        ∈ (Finset.range (n + 1)).filter (fun k => 2 ^ k ∣ n) := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hdvd⟩
    refine ⟨(n / d).primeFactorsList.length, hmemk, ?_⟩
    show n / 2 ^ (n / d).primeFactorsList.length = d
    rw [← hq]
    exact Nat.div_div_self hdn hn0
  · intro k hk
    rfl

end A084091Aux

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a084091.main := by
  intro n hn
  rw [A084091Aux.gf]
  simp only [PowerSeries.coeff_mk]
  exact A084091Aux.reindex n hn
