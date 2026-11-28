import OMAStatements.S_oeis_a143132
import Mathlib

namespace A143132

/-- The five surviving terms of the binomial transform. -/
def g (m : ℕ) : ℕ :=
  m.choose 0 * 1 + m.choose 1 * 5 + m.choose 2 * 15 + m.choose 3 * 35 + m.choose 4 * 70

lemma a_eq_g (m : ℕ) : OMA.S_oeis_a143132.a (m + 1) = g m := by
  unfold OMA.S_oeis_a143132.a g
  rw [Nat.add_sub_cancel]
  have h1 : ∑ k ∈ Finset.range (m + 1), m.choose k * OMA.S_oeis_a143132.b k =
      ∑ k ∈ Finset.range (m + 6), m.choose k * OMA.S_oeis_a143132.b k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    · intro k _ hk
      simp only [Finset.mem_range] at hk
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  have h2 : ∑ k ∈ Finset.range 5, m.choose k * OMA.S_oeis_a143132.b k =
      ∑ k ∈ Finset.range (m + 6), m.choose k * OMA.S_oeis_a143132.b k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    · intro k _ hk
      simp only [Finset.mem_range] at hk
      have : OMA.S_oeis_a143132.b k = 0 := by
        unfold OMA.S_oeis_a143132.b
        rw [if_neg (by omega)]
      rw [this, mul_zero]
  rw [h1, ← h2]
  simp [Finset.sum_range_succ, OMA.S_oeis_a143132.b, Nat.choose]

lemma g_period (m : ℕ) : g (m + 4) % 10 = g m % 10 := by
  unfold g
  simp only [Nat.choose_succ_succ', Nat.choose_zero_right, Nat.choose_one_right, Nat.reduceAdd,
    zero_add]
  omega

lemma g_mod (q : ℕ) : g (4 * q) % 10 = 1 ∧ g (4 * q + 1) % 10 = 6 ∧
    g (4 * q + 2) % 10 = 6 ∧ g (4 * q + 3) % 10 = 6 := by
  induction q with
  | zero => refine ⟨by decide, by decide, by decide, by decide⟩
  | succ q ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show 4 * (q + 1) = 4 * q + 4 by ring, g_period]; exact h0
    · rw [show 4 * (q + 1) + 1 = 4 * q + 1 + 4 by ring, g_period]; exact h1
    · rw [show 4 * (q + 1) + 2 = 4 * q + 2 + 4 by ring, g_period]; exact h2
    · rw [show 4 * (q + 1) + 3 = 4 * q + 3 + 4 by ring, g_period]; exact h3

end A143132

theorem OMA.solution : type_of% @OMA.S_oeis_a143132.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [A143132.a_eq_g]
  obtain ⟨h0, h1, h2, h3⟩ := A143132.g_mod (m / 4)
  have hm : m = 4 * (m / 4) + m % 4 := by omega
  have hlt : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3) with h | h | h | h
  · rw [if_pos (by omega), hm, h]; exact h0
  · rw [if_neg (by omega), hm, h]; exact h1
  · rw [if_neg (by omega), hm, h]; exact h2
  · rw [if_neg (by omega), hm, h]; exact h3
