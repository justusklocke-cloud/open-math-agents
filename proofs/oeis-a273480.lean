import OMAStatements.S_oeis_a273480
import Mathlib

namespace A273480Aux

def step (code : ℕ) (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun i j =>
  code.testBit ((g i j).toNat + 2 * ((g (i + 1) j).toNat +
      (g (i - 1) j).toNat + (g i (j + 1)).toNat + (g i (j - 1)).toNat))

open OMA.S_oeis_a273480 in
lemma cell_succ (code t : ℕ) : cell code (t + 1) = step code (cell code t) := by
  funext i j
  rw [cell]
  rfl

def pat (s : Bool) (L : List (ℤ × ℤ)) : ℤ → ℤ → Bool :=
  fun x y => if (x, y) ∈ L then !s else s

def inBox (L : List (ℤ × ℤ)) : Prop := ∀ p ∈ L, -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1

lemma pat_far (s : Bool) (L : List (ℤ × ℤ)) (hL : inBox L) (u v : ℤ)
    (h : ¬(-1 ≤ u ∧ u ≤ 1 ∧ -1 ≤ v ∧ v ≤ 1)) : pat s L u v = s := by
  unfold pat
  have hm : (u, v) ∉ L := fun hm => h (hL _ hm)
  simp [hm]

def five : List ℤ := [-2, -1, 0, 1, 2]

lemma mem_five (x : ℤ) (h1 : -2 ≤ x) (h2 : x ≤ 2) : x ∈ five := by
  unfold five
  simp
  omega

lemma step_pat (code : ℕ) (s s' : Bool) (L L' : List (ℤ × ℤ)) (hL : inBox L) (hL' : inBox L')
    (hr : code.testBit (s.toNat + 2 * (s.toNat + s.toNat + s.toNat + s.toNat)) = s')
    (hbox : ∀ x ∈ five, ∀ y ∈ five, step code (pat s L) x y = pat s' L' x y) :
    step code (pat s L) = pat s' L' := by
  funext x y
  by_cases h : (-2 ≤ x ∧ x ≤ 2) ∧ (-2 ≤ y ∧ y ≤ 2)
  · exact hbox x (mem_five x h.1.1 h.1.2) y (mem_five y h.2.1 h.2.2)
  · rw [pat_far s' L' hL' x y (by omega)]
    unfold step
    rw [pat_far s L hL x y (by omega), pat_far s L hL (x + 1) y (by omega),
      pat_far s L hL (x - 1) y (by omega), pat_far s L hL x (y + 1) (by omega),
      pat_far s L hL x (y - 1) (by omega)]
    exact hr

open OMA.S_oeis_a273480 in
lemma cell_zero (code : ℕ) : cell code 0 = pat false [(0, 0)] := by
  funext i j
  rw [cell]
  unfold pat
  by_cases h : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have : (i, j) ∉ [((0 : ℤ), (0 : ℤ))] := by
      simp only [List.mem_singleton, Prod.mk.injEq]
      exact h
    simp [h]

lemma single_count (p : ℤ × ℤ) (t : ℕ)
    (hp : -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t) :
    (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      if (((i : ℤ) - t, (j : ℤ) - t) = p) then (1 : ℤ) else 0) = 1 := by
  obtain ⟨a, b⟩ := p
  simp only at hp
  have hi0 : (a + t).toNat < 2 * t + 1 := by omega
  have hj0 : (b + t).toNat < 2 * t + 1 := by omega
  have h1 : ∀ i ∈ Finset.range (2 * t + 1), (∑ j ∈ Finset.range (2 * t + 1),
      if (((i : ℤ) - t, (j : ℤ) - t) = (a, b)) then (1 : ℤ) else 0) =
      if i = (a + t).toNat then 1 else 0 := by
    intro i _
    have h2 : ∀ j : ℕ, (((i : ℤ) - t, (j : ℤ) - t) = (a, b)) ↔
        (j = (b + t).toNat ∧ i = (a + t).toNat) := by
      intro j
      simp only [Prod.mk.injEq]
      omega
    simp only [h2]
    by_cases hi : i = (a + t).toNat
    · simp [hi, hj0]
    · simp [hi]
  rw [Finset.sum_congr rfl h1]
  simp [hi0]

def memCount (L : List (ℤ × ℤ)) (t : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
    if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then (1 : ℤ) else 0

lemma memCount_eq (t : ℕ) (ht : 1 ≤ t) (L : List (ℤ × ℤ)) (hnd : L.Nodup) (hin : inBox L) :
    memCount L t = L.length := by
  induction L with
  | nil => simp [memCount]
  | cons p L ih =>
    have hp : p ∉ L := (List.nodup_cons.mp hnd).1
    have hin' : inBox L := fun q hq => hin q (List.mem_cons_of_mem _ hq)
    have hpb := hin p List.mem_cons_self
    have key : ∀ i j : ℕ, (if (((i : ℤ) - t, (j : ℤ) - t) ∈ p :: L) then (1 : ℤ) else 0) =
        (if (((i : ℤ) - t, (j : ℤ) - t) = p) then (1 : ℤ) else 0) +
        (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then (1 : ℤ) else 0) := by
      intro i j
      by_cases h1 : ((i : ℤ) - t, (j : ℤ) - t) = p
      · have h2 : ((i : ℤ) - t, (j : ℤ) - t) ∉ L := by rw [h1]; exact hp
        simp [h1, hp]
      · simp [h1]
    have e : memCount (p :: L) t = 1 + memCount L t := by
      unfold memCount
      simp only [key, Finset.sum_add_distrib]
      rw [single_count p t (by omega)]
    rw [e, ih (List.nodup_cons.mp hnd).2 hin']
    simp
    ring

open OMA.S_oeis_a273480 in
lemma count_true (code t : ℕ) (ht : 1 ≤ t) (L : List (ℤ × ℤ)) (hnd : L.Nodup) (hin : inBox L)
    (h : cell code t = pat true L) :
    ((onCount code t : ℕ) : ℤ) = (2 * (t : ℤ) + 1) ^ 2 - L.length := by
  unfold onCount
  rw [h, ← memCount_eq t ht L hnd hin]
  unfold memCount
  push_cast
  have key : ∀ i j : ℕ, (if pat true L ((i : ℤ) - t) ((j : ℤ) - t) = true then (1 : ℤ) else 0) =
      1 - (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then (1 : ℤ) else 0) := by
    intro i j
    unfold pat
    by_cases h1 : ((i : ℤ) - t, (j : ℤ) - t) ∈ L
    · simp [h1]
    · simp [h1]
  simp only [key, Finset.sum_sub_distrib]
  simp
  ring


open OMA.S_oeis_a273480 in
lemma s1 : cell 737 1 = pat true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cell_succ, cell_zero]
  exact step_pat 737 false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a273480 in
lemma s2 : cell 737 2 = pat true [] := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, cell_succ, s1]
  exact step_pat 737 true true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a273480 in
lemma sper (k : ℕ) : cell 737 (k + 2) = pat true [] := by
  induction k with
  | zero => exact s2
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, cell_succ, ih]
    exact step_pat 737 true true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a273480 in
lemma on_big (n : ℕ) (hn : 2 ≤ n) :
    ((onCount 737 n : ℕ) : ℚ) = (2 * (n : ℚ) + 1) ^ 2 - 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h := count_true 737 (m + 2) (by omega) _ (by decide) (by unfold inBox; decide) (sper m)
  have h' : ((onCount 737 (m + 2) : ℕ) : ℚ) = (2 * ((m + 2 : ℕ) : ℚ) + 1) ^ 2 - 0 := by
    have h2 : ((onCount 737 (m + 2) : ℕ) : ℤ) = (2 * ((m + 2 : ℕ) : ℤ) + 1) ^ 2 - 0 := by
      rw [h]; norm_num
    exact_mod_cast h2
  exact h'

open OMA.S_oeis_a273480 in
lemma on_0 : ((onCount 737 0 : ℕ) : ℚ) = 1 := by
  have h : onCount 737 0 = 1 := by decide
  rw [h]; norm_num

open OMA.S_oeis_a273480 in
lemma on_1 : ((onCount 737 1 : ℕ) : ℚ) = 4 := by
  have h2 : ((onCount 737 1 : ℕ) : ℤ) = 4 := by
    rw [count_true 737 1 (by norm_num) _ (by decide) (by unfold inBox; decide) s1]; norm_num
  exact_mod_cast h2

open OMA.S_oeis_a273480 in
lemma on_2 : ((onCount 737 2 : ℕ) : ℚ) = 25 := by
  rw [on_big 2 (by norm_num)]; norm_num

open OMA.S_oeis_a273480 in
lemma on_3 : ((onCount 737 3 : ℕ) : ℚ) = 49 := by
  rw [on_big 3 (by norm_num)]; norm_num

open OMA.S_oeis_a273480 in
lemma on_4 : ((onCount 737 4 : ℕ) : ℚ) = 81 := by
  rw [on_big 4 (by norm_num)]; norm_num

open OMA.S_oeis_a273480 in
lemma on_5 : ((onCount 737 5 : ℕ) : ℚ) = 121 := by
  rw [on_big 5 (by norm_num)]; norm_num

open OMA.S_oeis_a273480 in
lemma on_6 : ((onCount 737 6 : ℕ) : ℚ) = 169 := by
  rw [on_big 6 (by norm_num)]; norm_num

open OMA.S_oeis_a273480 in
lemma a_succ (n : ℕ) : (a (n + 1) : ℚ) = (a n : ℚ) + ((onCount 737 (n + 1) : ℕ) : ℚ) := by
  unfold a
  rw [Finset.sum_range_succ]
  push_cast
  ring

open OMA.S_oeis_a273480 in
lemma a_0 : (a 0 : ℚ) = 1 := by
  unfold a
  rw [Finset.sum_range_one]
  exact_mod_cast on_0

open OMA.S_oeis_a273480 in
lemma a_1 : (a 1 : ℚ) = 5 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, a_succ, a_0, on_1]; norm_num

open OMA.S_oeis_a273480 in
lemma a_2 : (a 2 : ℚ) = 30 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, a_succ, a_1, on_2]; norm_num

open OMA.S_oeis_a273480 in
lemma a_3 : (a 3 : ℚ) = 79 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, a_succ, a_2, on_3]; norm_num

open OMA.S_oeis_a273480 in
lemma a_4 : (a 4 : ℚ) = 160 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, a_succ, a_3, on_4]; norm_num

open OMA.S_oeis_a273480 in
lemma a_5 : (a 5 : ℚ) = 281 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, a_succ, a_4, on_5]; norm_num

open OMA.S_oeis_a273480 in
lemma a_cl (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (4 * (n : ℚ) ^ 3 + 12 * (n : ℚ) ^ 2 + 11 * (n : ℚ) - 12) / 3 := by
  have hge : 1 ≤ n := hn
  induction n, hge using Nat.le_induction with
  | base => rw [a_1]; norm_num
  | succ n hn2 ih =>
    rw [a_succ, ih (by omega), on_big (n + 1) (by omega)]
    push_cast
    ring

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A273480Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a273480 A273480Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a273480.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    refine (a_cl n (by omega)).trans ?_
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    rw [a_cl (m + 5) (by omega), a_cl (m + 4) (by omega), a_cl (m + 3) (by omega), a_cl (m + 2) (by omega), a_cl (m + 1) (by omega)]
    push_cast
    ring
  · have hD : ((1 - PowerSeries.X) ^ 4 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-4) * PowerSeries.X ^ 1 + PowerSeries.C 6 * PowerSeries.X ^ 2 + PowerSeries.C (-4) * PowerSeries.X ^ 3 + PowerSeries.C 1 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + PowerSeries.X + 16 * PowerSeries.X ^ 2 - 15 * PowerSeries.X ^ 3 + 5 * PowerSeries.X ^ 4 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 1 * PowerSeries.X ^ 1 + PowerSeries.C 16 * PowerSeries.X ^ 2 + PowerSeries.C (-15) * PowerSeries.X ^ 3 + PowerSeries.C 5 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | n
    · simp [a_0] <;> norm_num
    · simp [a_0, a_1] <;> norm_num
    · simp [a_0, a_1, a_2] <;> norm_num
    · simp [a_0, a_1, a_2, a_3] <;> norm_num
    · simp [a_0, a_1, a_2, a_3, a_4] <;> norm_num
    · have f0 := a_cl (n + 5) (by omega)
      have f1 := a_cl (n + 4) (by omega)
      have f2 := a_cl (n + 3) (by omega)
      have f3 := a_cl (n + 2) (by omega)
      have f4 := a_cl (n + 1) (by omega)
      simp [f0, f1, f2, f3, f4]
      ring
