import OMAStatements.S_oeis_a112701
import Mathlib

namespace A112701

lemma cat_rec (k : ℕ) : (k + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  have h4 : (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * (2 * (2 * k + 1) * catalan k) := by
    calc (k + 1) * ((k + 2) * catalan (k + 1))
        = (k + 1) * ((k + 1 + 1) * catalan (k + 1)) := by ring
      _ = (k + 1) * (k + 1).centralBinom := by rw [h1]
      _ = 2 * (2 * k + 1) * k.centralBinom := h3
      _ = 2 * (2 * k + 1) * ((k + 1) * catalan k) := by rw [h2]
      _ = (k + 1) * (2 * (2 * k + 1) * catalan k) := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) h4

lemma a_succ (m : ℕ) : OMA.S_oeis_a112701.a (m + 1)
    = OMA.S_oeis_a112701.a m + catalan (m + 1) * 7 ^ (m + 1) := by
  unfold OMA.S_oeis_a112701.a
  exact Finset.sum_range_succ _ (m + 1)

end A112701

theorem OMA.solution : type_of% @OMA.S_oeis_a112701.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2]
  have s2 := A112701.a_succ (m + 1)
  have s1 := A112701.a_succ m
  have hc := A112701.cat_rec (m + 1)
  have hcz : ((m : ℤ) + 3) * (catalan (m + 2) : ℤ)
      = 2 * (2 * ((m : ℤ) + 1) + 1) * (catalan (m + 1) : ℤ) := by exact_mod_cast hc
  have t2 : (OMA.S_oeis_a112701.a (m + 2) : ℤ) = (OMA.S_oeis_a112701.a (m + 1) : ℤ)
      + (catalan (m + 2) : ℤ) * 7 * 7 ^ (m + 1) := by
    rw [s2]; push_cast; ring
  have t1 : (OMA.S_oeis_a112701.a (m + 1) : ℤ) = (OMA.S_oeis_a112701.a m : ℤ)
      + (catalan (m + 1) : ℤ) * 7 ^ (m + 1) := by
    rw [s1]; push_cast; ring
  rw [t2, t1]
  push_cast
  linear_combination (7 * 7 ^ (m + 1) : ℤ) * hcz
