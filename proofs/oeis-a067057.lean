import OMAStatements.S_oeis_a067057
import Mathlib

namespace A067057
open OMA.S_oeis_a067057

/-- The element sum of a finite set, in the integers. -/
def sg (S : Finset ℕ) : ℤ := ∑ i ∈ S, (i : ℤ)

/-- 1 + 2 + ... + n. -/
def tau (n : ℕ) : ℤ := sg (Finset.Icc 1 n)

/-- The sum over all subsets S of sum(S) * (sum of the complement). -/
def g (n : ℕ) : ℤ := ∑ S ∈ (Finset.Icc 1 n).powerset, sg S * (tau n - sg S)

lemma Icc_succ (n : ℕ) : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

lemma notMem (n : ℕ) : n + 1 ∉ Finset.Icc 1 n := by
  simp only [Finset.mem_Icc]
  omega

lemma tau_succ (n : ℕ) : tau (n + 1) = tau n + ((n : ℤ) + 1) := by
  unfold tau sg
  rw [Icc_succ, Finset.sum_insert (notMem n)]
  push_cast
  ring

lemma two_tau (n : ℕ) : 2 * tau n = (n : ℤ) * ((n : ℤ) + 1) := by
  induction n with
  | zero => simp [tau, sg]
  | succ n ih =>
    rw [tau_succ]
    push_cast
    linear_combination ih

lemma g_succ (n : ℕ) : g (n + 1) = 2 * g n + ((n : ℤ) + 1) * 2 ^ n * tau n := by
  unfold g
  rw [Icc_succ, Finset.sum_powerset_insert (notMem n)]
  have h2 : ∀ S ∈ (Finset.Icc 1 n).powerset,
      sg (insert (n + 1) S) * (tau (n + 1) - sg (insert (n + 1) S)) =
        ((n : ℤ) + 1 + sg S) * (tau n - sg S) := by
    intro S hS
    have hS' : n + 1 ∉ S := fun h => notMem n (Finset.mem_powerset.mp hS h)
    have e : sg (insert (n + 1) S) = (n : ℤ) + 1 + sg S := by
      unfold sg
      rw [Finset.sum_insert hS']
      push_cast
      ring
    rw [e, tau_succ]
    ring
  rw [Finset.sum_congr rfl h2, tau_succ, ← Finset.sum_add_distrib]
  have h3 : ∀ S ∈ (Finset.Icc 1 n).powerset,
      sg S * (tau n + ((n : ℤ) + 1) - sg S) + ((n : ℤ) + 1 + sg S) * (tau n - sg S) =
        2 * (sg S * (tau n - sg S)) + ((n : ℤ) + 1) * tau n := by
    intro S _
    ring
  rw [Finset.sum_congr rfl h3, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_powerset, Nat.card_Icc, nsmul_eq_mul]
  rw [show n + 1 - 1 = n by omega]
  push_cast
  ring

lemma g_closed (n : ℕ) :
    48 * g n = 2 ^ n * ((n : ℤ) - 1) * n * ((n : ℤ) + 1) * (3 * (n : ℤ) + 2) := by
  induction n with
  | zero => simp [g, sg, tau]
  | succ n ih =>
    rw [g_succ]
    have ht := two_tau n
    push_cast
    linear_combination 2 * ih + 24 * ((n : ℤ) + 1) * 2 ^ n * ht

lemma g_even (n : ℕ) : ∃ c : ℤ, g n = 2 * c := by
  induction n with
  | zero => exact ⟨0, by simp [g, sg, tau]⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      refine ⟨g 0, ?_⟩
      rw [g_succ]
      simp [tau, sg]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      refine ⟨g (k + 1) + (((k + 1 : ℕ) : ℤ) + 1) * 2 ^ k * tau (k + 1), ?_⟩
      rw [g_succ]
      ring

/-- The natural-number sum in the definition of a. -/
def N (n : ℕ) : ℕ :=
  ∑ S ∈ (Finset.Icc 1 n).powerset, (∑ i ∈ S, i) * (∑ i ∈ Finset.Icc 1 n \ S, i)

lemma N_cast (n : ℕ) : (N n : ℤ) = g n := by
  unfold N g
  push_cast
  apply Finset.sum_congr rfl
  intro S hS
  have hsub : S ⊆ Finset.Icc 1 n := Finset.mem_powerset.mp hS
  have h := Finset.sum_sdiff (f := fun i : ℕ => (i : ℤ)) hsub
  unfold tau sg
  rw [← h]
  ring

lemma a_closed (n : ℕ) :
    96 * (a n : ℤ) = 2 ^ n * ((n : ℤ) - 1) * n * ((n : ℤ) + 1) * (3 * (n : ℤ) + 2) := by
  obtain ⟨c, hc⟩ := g_even n
  have hN := N_cast n
  have h2 : 2 ∣ N n := by
    have : (2 : ℤ) ∣ (N n : ℤ) := ⟨c, by rw [hN, hc]⟩
    exact_mod_cast this
  have h3 : a n * 2 = N n := Nat.div_mul_cancel h2
  have h4 : (a n : ℤ) * 2 = g n := by
    rw [← hN, ← h3]
    push_cast
    ring
  linear_combination 48 * h4 + g_closed n

lemma A_eq : A = PowerSeries.mk (fun n => (a n : ℤ)) := by
  unfold A
  congr 1
  funext n
  split_ifs with h
  · subst h
    have h0 := a_closed 0
    simp at h0
    simp [h0]
  · rfl

lemma coeff_mk_mul_X (k n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk (fun n => (a n : ℤ)) * PowerSeries.X ^ k) =
      if k ≤ n then (a (n - k) : ℤ) else 0 := by
  simp only [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]

lemma coeff_lhs (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk (fun n => (a n : ℤ)) * (2 * PowerSeries.X - 1) ^ 5) =
      32 * (if 5 ≤ n then (a (n - 5) : ℤ) else 0) - 80 * (if 4 ≤ n then (a (n - 4) : ℤ) else 0)
        + 80 * (if 3 ≤ n then (a (n - 3) : ℤ) else 0) - 40 * (if 2 ≤ n then (a (n - 2) : ℤ) else 0)
        + 10 * (if 1 ≤ n then (a (n - 1) : ℤ) else 0) - (a n : ℤ) := by
  have expand : PowerSeries.mk (fun n => (a n : ℤ)) * (2 * PowerSeries.X - 1) ^ 5 =
      PowerSeries.C 32 * (PowerSeries.mk (fun n => (a n : ℤ)) * PowerSeries.X ^ 5)
        - PowerSeries.C 80 * (PowerSeries.mk (fun n => (a n : ℤ)) * PowerSeries.X ^ 4)
        + PowerSeries.C 80 * (PowerSeries.mk (fun n => (a n : ℤ)) * PowerSeries.X ^ 3)
        - PowerSeries.C 40 * (PowerSeries.mk (fun n => (a n : ℤ)) * PowerSeries.X ^ 2)
        + PowerSeries.C 10 * (PowerSeries.mk (fun n => (a n : ℤ)) * PowerSeries.X ^ 1)
        - PowerSeries.mk (fun n => (a n : ℤ)) := by
    simp only [map_ofNat, pow_one]
    ring
  rw [expand]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_mk_mul_X]
  simp only [PowerSeries.coeff_mk]

lemma coeff_rhs (n : ℕ) :
    PowerSeries.coeff n (-2 * (PowerSeries.X : PowerSeries ℤ) ^ 2 * (PowerSeries.X + 1)) =
      -2 * (if n = 3 then 1 else 0) - 2 * (if n = 2 then 1 else 0) := by
  have expand : (-2 * (PowerSeries.X : PowerSeries ℤ) ^ 2 * (PowerSeries.X + 1)) =
      - (PowerSeries.C 2 * PowerSeries.X ^ 3) - PowerSeries.C 2 * PowerSeries.X ^ 2 := by
    simp only [map_ofNat]
    ring
  rw [expand]
  simp only [map_sub, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  ring

end A067057

theorem OMA.solution : type_of% @OMA.S_oeis_a067057.main := by
  rw [A067057.A_eq]
  apply PowerSeries.ext
  intro n
  rw [A067057.coeff_lhs, A067057.coeff_rhs]
  by_cases hn : 5 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have e1 : m + 5 - 1 = m + 4 := by omega
    have e2 : m + 5 - 2 = m + 3 := by omega
    have e3 : m + 5 - 3 = m + 2 := by omega
    have e4 : m + 5 - 4 = m + 1 := by omega
    have e5 : m + 5 - 5 = m := by omega
    have c1 : 1 ≤ m + 5 := by omega
    have c2 : 2 ≤ m + 5 := by omega
    have c3 : 3 ≤ m + 5 := by omega
    have c4 : 4 ≤ m + 5 := by omega
    have c5 : 5 ≤ m + 5 := by omega
    have d2 : ¬ (m + 5 = 2) := by omega
    have d3 : ¬ (m + 5 = 3) := by omega
    rw [if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_pos c5, if_neg d2, if_neg d3,
      e1, e2, e3, e4, e5]
    have h0 := A067057.a_closed m
    have h1 := A067057.a_closed (m + 1)
    have h2 := A067057.a_closed (m + 2)
    have h3 := A067057.a_closed (m + 3)
    have h4 := A067057.a_closed (m + 4)
    have h5 := A067057.a_closed (m + 5)
    push_cast at h0 h1 h2 h3 h4 h5
    have key : 96 * (32 * (OMA.S_oeis_a067057.a m : ℤ) - 80 * (OMA.S_oeis_a067057.a (m + 1) : ℤ)
        + 80 * (OMA.S_oeis_a067057.a (m + 2) : ℤ) - 40 * (OMA.S_oeis_a067057.a (m + 3) : ℤ)
        + 10 * (OMA.S_oeis_a067057.a (m + 4) : ℤ) - (OMA.S_oeis_a067057.a (m + 5) : ℤ)) = 0 := by
      linear_combination 32 * h0 - 80 * h1 + 80 * h2 - 40 * h3 + 10 * h4 - h5
    omega
  · have hn' : n < 5 := by omega
    have h0 := A067057.a_closed 0
    have h1 := A067057.a_closed 1
    have h2 := A067057.a_closed 2
    have h3 := A067057.a_closed 3
    have h4 := A067057.a_closed 4
    norm_num at h0 h1 h2 h3 h4
    interval_cases n <;> norm_num <;> omega
