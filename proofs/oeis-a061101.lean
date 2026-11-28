import OMAStatements.S_oeis_a061101
import Mathlib

namespace A061101Aux

open OMA.S_oeis_a061101 in
lemma dr_spec : ∀ m : ℕ, digitalRoot m < 10 ∧ digitalRoot m % 9 = m % 9 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [digitalRoot]
    by_cases h : m < 10
    · rw [dif_pos h]
      exact ⟨h, rfl⟩
    · rw [dif_neg h]
      have hlt : (Nat.digits 10 m).sum < m := by
        rw [Nat.digits_def' (by norm_num) (by omega), List.sum_cons]
        have hle := Nat.digit_sum_le 10 (m / 10)
        omega
      obtain ⟨h1, h2⟩ := ih _ hlt
      refine ⟨h1, ?_⟩
      rw [h2]
      exact (Nat.modEq_nine_digits_sum m).symm

open OMA.S_oeis_a061101 in
lemma dr_seven (m : ℕ) : digitalRoot m = 7 ↔ m % 9 = 7 := by
  obtain ⟨h1, h2⟩ := dr_spec m
  constructor
  · intro h
    rw [h] at h2
    omega
  · intro h
    omega

def kk (j : ℕ) : ℕ := 9 * (j / 2) + 4 + j % 2

lemma kk_lt (j : ℕ) : kk j < kk (j + 1) := by
  unfold kk
  omega

lemma f_mono : StrictMono (fun j => kk j * kk j) := by
  apply strictMono_nat_of_lt_succ
  intro j
  exact Nat.mul_self_lt_mul_self (kk_lt j)

lemma sq_mod (k : ℕ) : (k * k) % 9 = 7 ↔ (k % 9 = 4 ∨ k % 9 = 5) := by
  have h : (k * k) % 9 = ((k % 9) * (k % 9)) % 9 := Nat.mul_mod k k 9
  have hk : k % 9 < 9 := Nat.mod_lt _ (by norm_num)
  rw [h]
  generalize k % 9 = r at hk ⊢
  interval_cases r <;> decide

open OMA.S_oeis_a061101 in
lemma range_eq : Set.range (fun j => kk j * kk j) = Set.ofPred P := by
  apply Set.ext
  intro m
  constructor
  · rintro ⟨j, rfl⟩
    show IsSquare (kk j * kk j) ∧ digitalRoot (kk j * kk j) = 7
    refine ⟨⟨kk j, rfl⟩, ?_⟩
    rw [dr_seven, sq_mod]
    unfold kk
    omega
  · intro hm
    obtain ⟨⟨k, rfl⟩, h7⟩ : IsSquare m ∧ digitalRoot m = 7 := hm
    rw [dr_seven, sq_mod] at h7
    rcases h7 with h | h
    · refine ⟨2 * (k / 9), ?_⟩
      have e : kk (2 * (k / 9)) = k := by
        unfold kk
        omega
      show kk (2 * (k / 9)) * kk (2 * (k / 9)) = k * k
      rw [e]
    · refine ⟨2 * (k / 9) + 1, ?_⟩
      have e : kk (2 * (k / 9) + 1) = k := by
        unfold kk
        omega
      show kk (2 * (k / 9) + 1) * kk (2 * (k / 9) + 1) = k * k
      rw [e]

open OMA.S_oeis_a061101 in
lemma nth_eq : Nat.nth P = fun j => kk j * kk j := by
  have hinf : (Set.ofPred P).Infinite := by
    rw [← range_eq]
    exact Set.infinite_range_of_injective f_mono.injective
  exact ((Nat.nth_strictMono hinf).range_inj f_mono).mp
    ((Nat.range_nth_of_infinite hinf).trans range_eq.symm)

end A061101Aux

open OMA.S_oeis_a061101 in
theorem OMA.solution : type_of% @OMA.S_oeis_a061101.main := by
  intro n hn
  have hval : a n = A061101Aux.kk (n - 1) * A061101Aux.kk (n - 1) := by
    unfold a
    rw [A061101Aux.nth_eq]
  constructor
  · rintro ⟨t, ht⟩
    have hk : A061101Aux.kk (n - 1) = 9 * t - 4 := by
      unfold A061101Aux.kk
      omega
    rw [hval, hk]
    have e : (9 * n - 8) ^ 2 = 4 * ((9 * t - 4) * (9 * t - 4)) := by
      have e2 : 9 * n - 8 = 2 * (9 * t - 4) := by omega
      rw [e2]
      ring
    rw [e, Nat.mul_div_cancel_left _ (by norm_num)]
  · rintro ⟨t, ht⟩
    have hk : A061101Aux.kk (n - 1) = 9 * t + 4 := by
      unfold A061101Aux.kk
      omega
    rw [hval, hk]
    have e : (9 * n - 1) ^ 2 = 4 * ((9 * t + 4) * (9 * t + 4)) := by
      have e2 : 9 * n - 1 = 2 * (9 * t + 4) := by omega
      rw [e2]
      ring
    rw [e, Nat.mul_div_cancel_left _ (by norm_num)]
