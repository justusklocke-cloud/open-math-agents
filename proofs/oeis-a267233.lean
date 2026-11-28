import OMAStatements.S_oeis_a267233
import Mathlib

namespace A267233

lemma ite_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    (if p then (1 : ℚ) else 0) = if q then 1 else 0 := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

lemma allowed_eq (a c d : ℕ) : OMA.S_oeis_a267233.allowed a a c d ↔ (c < a ∧ d < a) := by
  unfold OMA.S_oeis_a267233.allowed
  rw [if_pos rfl]

lemma allowed_ne (a b c d : ℕ) (h : a ≠ b) :
    OMA.S_oeis_a267233.allowed a b c d ↔ (b = c → d < b) := by
  unfold OMA.S_oeis_a267233.allowed
  rw [if_neg h]
  by_cases h2 : b = c
  · rw [if_pos h2]; exact ⟨fun h _ => h, fun h => h h2⟩
  · rw [if_neg h2]; exact ⟨fun _ h => absurd h h2, fun _ => trivial⟩

open Finset in
lemma sum_lt (n a : ℕ) (ha : a ≤ n) :
    ∑ d ∈ range (n + 1), (if d < a then (1 : ℚ) else 0) = a := by
  rw [Finset.sum_boole]
  have h : (range (n + 1)).filter (fun d => d < a) = range a := by
    ext d; simp only [mem_filter, mem_range]; omega
  rw [h, card_range]

open Finset in
lemma sum_ite1 (n b : ℕ) (x y : ℚ) (hb : b ≤ n) :
    ∑ c ∈ range (n + 1), (if b = c then x else y) = x + n * y := by
  have h : ∀ c : ℕ, (if b = c then x else y) = y + (if b = c then x - y else 0) := by
    intro c; split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, Finset.sum_ite_eq,
    Finset.mem_range]
  rw [if_pos (by omega)]
  simp only [nsmul_eq_mul]
  push_cast
  ring

open Finset in
lemma sum_ite2 (n b : ℕ) (x y : ℚ) (hb : b ≤ n) :
    ∑ c ∈ range (n + 1), (if c = b then x else y) = x + n * y := by
  rw [← sum_ite1 n b x y hb]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : c = b
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

open Finset in
lemma inner_eq (n a : ℕ) (ha : a ≤ n) :
    ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1),
      (if OMA.S_oeis_a267233.allowed a a c d then (1 : ℚ) else 0) = (a : ℚ) ^ 2 := by
  have h : ∀ c d : ℕ, (if OMA.S_oeis_a267233.allowed a a c d then (1 : ℚ) else 0)
      = (if c < a then (1 : ℚ) else 0) * (if d < a then (1 : ℚ) else 0) := by
    intro c d
    rw [ite_iff (allowed_eq a c d)]
    by_cases h1 : c < a <;> by_cases h2 : d < a <;> simp [h1, h2]
  simp only [h]
  rw [← Finset.sum_mul_sum, sum_lt n a ha]
  ring

open Finset in
lemma inner_ne (n a b : ℕ) (hab : a ≠ b) (hb : b ≤ n) :
    ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1),
      (if OMA.S_oeis_a267233.allowed a b c d then (1 : ℚ) else 0) = (b : ℚ) + n * (n + 1) := by
  have h : ∀ c : ℕ, ∑ d ∈ range (n + 1),
      (if OMA.S_oeis_a267233.allowed a b c d then (1 : ℚ) else 0)
        = if b = c then (b : ℚ) else (n + 1) := by
    intro c
    by_cases hbc : b = c
    · rw [if_pos hbc, ← sum_lt n b hb]
      apply Finset.sum_congr rfl
      intro d _
      rw [ite_iff (allowed_ne a b c d hab)]
      exact ite_iff ⟨fun h => h hbc, fun h _ => h⟩
    · rw [if_neg hbc]
      have h1 : ∀ d ∈ range (n + 1),
          (if OMA.S_oeis_a267233.allowed a b c d then (1 : ℚ) else 0) = 1 := by
        intro d _
        rw [if_pos ((allowed_ne a b c d hab).mpr (fun h => absurd h hbc))]
      rw [Finset.sum_congr rfl h1]
      simp
  simp only [h]
  exact sum_ite1 n b _ _ hb

open Finset in
lemma sumb (n m : ℕ) :
    ∑ b ∈ range (m + 1), ((b : ℚ) ^ 2 + n * ((b : ℚ) + n * (n + 1)))
      = (m : ℚ) * (m + 1) * (2 * m + 1) / 6 + n * ((m : ℚ) * (m + 1) / 2 + (m + 1) * (n * (n + 1))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

open Finset in
lemma count_eq (n : ℕ) :
    OMA.S_oeis_a267233.count n = (n : ℚ) ^ 4 + 17 / 6 * n ^ 3 + 2 * n ^ 2 + 1 / 6 * n := by
  unfold OMA.S_oeis_a267233.count
  have hG : ∀ b ∈ range (n + 1), ∀ a ∈ range (n + 1),
      ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1),
        (if OMA.S_oeis_a267233.allowed a b c d then (1 : ℚ) else 0)
        = if a = b then (b : ℚ) ^ 2 else ((b : ℚ) + n * (n + 1)) := by
    intro b hb a ha
    rw [mem_range] at hb ha
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl]; exact inner_eq n a (by omega)
    · rw [if_neg hab]; exact inner_ne n a b hab (by omega)
  have hA : ∀ b ∈ range (n + 1), ∑ a ∈ range (n + 1), ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1),
      (if OMA.S_oeis_a267233.allowed a b c d then (1 : ℚ) else 0)
        = (b : ℚ) ^ 2 + n * ((b : ℚ) + n * (n + 1)) := by
    intro b hb
    rw [Finset.sum_congr rfl (hG b hb)]
    exact sum_ite2 n b _ _ (by rw [mem_range] at hb; omega)
  rw [Finset.sum_congr rfl hA, sumb]
  ring

lemma terms_eq (n : ℕ) :
    OMA.S_oeis_a267233.terms n = (n : ℚ) ^ 4 + 17 / 6 * n ^ 3 + 2 * n ^ 2 + 1 / 6 * n := by
  cases n with
  | zero => simp [OMA.S_oeis_a267233.terms]
  | succ m =>
    show OMA.S_oeis_a267233.count (m + 1) = _
    exact count_eq (m + 1)

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267233

set_option maxHeartbeats 1600000 in
open A267233 in
theorem OMA.solution : type_of% @OMA.S_oeis_a267233.main := by
  refine ⟨count_eq, ?_, ?_⟩
  · intro n
    simp only [terms_eq]
    push_cast
    ring
  · rw [mul_comm]
    have hD : ((1 - PowerSeries.X) ^ 5 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-5) * PowerSeries.X ^ 1 +
        PowerSeries.C 10 * PowerSeries.X ^ 2 + PowerSeries.C (-10) * PowerSeries.X ^ 3 +
        PowerSeries.C 5 * PowerSeries.X ^ 4 + PowerSeries.C (-1) * PowerSeries.X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (PowerSeries.X * (6 + 17 * PowerSeries.X + PowerSeries.X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C 6 * PowerSeries.X ^ 1 + PowerSeries.C 17 * PowerSeries.X ^ 2 +
        PowerSeries.C 1 * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow, terms_eq]
    rcases n with _ | _ | _ | _ | _ | n
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · simp
      ring
