import OMAStatements.S_oeis_a273850
import Mathlib

namespace CAOEISA273850Aux


def pat (b : Bool) (L : List (ℤ × ℤ)) : ℤ → ℤ → Bool := fun i j => if (i, j) ∈ L then !b else b

def inBox (L : List (ℤ × ℤ)) : Prop := ∀ p ∈ L, -2 ≤ p.1 ∧ p.1 ≤ 2 ∧ -2 ≤ p.2 ∧ p.2 ≤ 2

lemma pat_far (b : Bool) (L : List (ℤ × ℤ)) (hL : inBox L) (u v : ℤ)
    (h : ¬(-2 ≤ u ∧ u ≤ 2 ∧ -2 ≤ v ∧ v ≤ 2)) : pat b L u v = b := by
  unfold pat
  have hm : (u, v) ∉ L := fun hm => h (hL _ hm)
  simp [hm]

def seven : List ℤ := [-3, -2, -1, 0, 1, 2, 3]

lemma mem_seven (x : ℤ) (h1 : -3 ≤ x) (h2 : x ≤ 3) : x ∈ seven := by
  unfold seven
  simp
  omega

def nxt (code : ℕ) (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun i j =>
  code.testBit ((g i j).toNat + 2 * ((g (i + 1) j).toNat + (g (i - 1) j).toNat +
    (g i (j + 1)).toNat + (g i (j - 1)).toNat))

open OMA.S_oeis_a273850 in
lemma cell_succ (code t : ℕ) : cell code (t + 1) = nxt code (cell code t) := by
  funext i j
  rw [cell]
  rfl

open OMA.S_oeis_a273850 in
lemma cell_zero (code : ℕ) : cell code 0 = pat false [(0, 0)] := by
  funext i j
  unfold pat
  rw [cell]
  by_cases h : i = 0 ∧ j = 0
  · simp [h]
  · have h' : ¬ ((i, j) = ((0 : ℤ), (0 : ℤ))) := fun e => h (Prod.mk.injEq _ _ _ _ |>.mp e)
    simp [h, h']

lemma step_pat (code : ℕ) (b b' : Bool) (L L' : List (ℤ × ℤ)) (hL : inBox L) (hL' : inBox L')
    (hr : code.testBit (b.toNat + 2 * (b.toNat + b.toNat + b.toNat + b.toNat)) = b')
    (hbox : ∀ x ∈ seven, ∀ y ∈ seven, nxt code (pat b L) x y = pat b' L' x y) :
    nxt code (pat b L) = pat b' L' := by
  funext x y
  by_cases h : (-3 ≤ x ∧ x ≤ 3) ∧ (-3 ≤ y ∧ y ≤ 3)
  · exact hbox x (mem_seven x h.1.1 h.1.2) y (mem_seven y h.2.1 h.2.2)
  · rw [pat_far b' L' hL' x y (by omega)]
    unfold nxt
    rw [pat_far b L hL x y (by omega), pat_far b L hL (x + 1) y (by omega),
      pat_far b L hL (x - 1) y (by omega), pat_far b L hL x (y + 1) (by omega),
      pat_far b L hL x (y - 1) (by omega)]
    exact hr

lemma count_single (t : ℕ) (p : ℤ × ℤ)
    (h : -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if (((i : ℤ) - t, (j : ℤ) - t) = p) then 1 else 0) = 1 := by
  obtain ⟨p1, p2⟩ := p
  simp only at h
  have e1 : (((p1 + t).toNat : ℕ) : ℤ) = p1 + t := Int.toNat_of_nonneg (by omega)
  have e2 : (((p2 + t).toNat : ℕ) : ℤ) = p2 + t := Int.toNat_of_nonneg (by omega)
  rw [Finset.sum_eq_single (p1 + t).toNat]
  · rw [Finset.sum_eq_single (p2 + t).toNat]
    · rw [if_pos]
      rw [e1, e2]
      simp
    · intro j _ hj
      rw [if_neg]
      intro heq
      apply hj
      have h2 := (Prod.mk.injEq _ _ _ _ |>.mp heq).2
      omega
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_range]
      omega
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro heq
    apply hi
    have h1 := (Prod.mk.injEq _ _ _ _ |>.mp heq).1
    omega
  · intro hn
    exfalso
    apply hn
    rw [Finset.mem_range]
    omega

lemma count_mem (t : ℕ) (L : List (ℤ × ℤ)) (hn : L.Nodup)
    (hb : ∀ p ∈ L, -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then 1 else 0) = L.length := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp : p ∉ L := (List.nodup_cons.mp hn).1
    have hn' : L.Nodup := (List.nodup_cons.mp hn).2
    have e : ∀ i j : ℕ, (if (((i : ℤ) - t, (j : ℤ) - t) ∈ p :: L) then 1 else 0) =
        (if (((i : ℤ) - t, (j : ℤ) - t) = p) then 1 else 0) +
        (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then 1 else 0) := by
      intro i j
      by_cases h1 : ((i : ℤ) - t, (j : ℤ) - t) = p
      · have h2 : ((i : ℤ) - t, (j : ℤ) - t) ∉ L := by rw [h1]; exact hp
        rw [if_pos (by rw [h1]; exact List.mem_cons_self), if_pos h1, if_neg h2]
      · by_cases h3 : ((i : ℤ) - t, (j : ℤ) - t) ∈ L
        · rw [if_pos (List.mem_cons_of_mem _ h3), if_neg h1, if_pos h3]
        · rw [if_neg (by
            intro hm
            rcases List.mem_cons.mp hm with h4 | h4
            · exact h1 h4
            · exact h3 h4), if_neg h1, if_neg h3]
    simp only [e, Finset.sum_add_distrib]
    rw [count_single t p (hb p List.mem_cons_self),
      ih hn' (fun q hq => hb q (List.mem_cons_of_mem _ hq))]
    simp [add_comm]

open OMA.S_oeis_a273850 in
lemma onCount_false (code t : ℕ) (L : List (ℤ × ℤ)) (c : ℕ) (hc : L.length = c) (hn : L.Nodup)
    (hb : ∀ p ∈ L, -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t)
    (h : cell code t = pat false L) : onCount code t = c := by
  unfold onCount
  rw [h, ← hc, ← count_mem t L hn hb]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold pat
  by_cases hm : ((i : ℤ) - t, (j : ℤ) - t) ∈ L <;> simp [hm]

open OMA.S_oeis_a273850 in
lemma onCount_true (code t : ℕ) (L : List (ℤ × ℤ)) (c : ℕ) (hc : L.length = c) (hn : L.Nodup)
    (hb : ∀ p ∈ L, -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t)
    (h : cell code t = pat true L) : onCount code t + c = (2 * t + 1) ^ 2 := by
  unfold onCount
  rw [h, ← hc, ← count_mem t L hn hb, ← Finset.sum_add_distrib]
  have e : ∀ i ∈ Finset.range (2 * t + 1),
      (∑ j ∈ Finset.range (2 * t + 1), (if pat true L ((i : ℤ) - t) ((j : ℤ) - t) = true then 1 else 0)
        + ∑ j ∈ Finset.range (2 * t + 1), (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then 1 else 0))
      = 2 * t + 1 := by
    intro i _
    rw [← Finset.sum_add_distrib]
    have e2 : ∀ j ∈ Finset.range (2 * t + 1),
        ((if pat true L ((i : ℤ) - t) ((j : ℤ) - t) = true then 1 else 0)
          + (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then 1 else 0) : ℕ) = 1 := by
      intro j _
      unfold pat
      by_cases hm : ((i : ℤ) - t, (j : ℤ) - t) ∈ L <;> simp [hm]
    rw [Finset.sum_congr rfl e2]
    simp
  rw [Finset.sum_congr rfl e]
  simp
  ring


open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

open OMA.S_oeis_a273850 in
lemma st0 : cell 969 0 = pat false [(0, 0)] := cell_zero 969

open OMA.S_oeis_a273850 in
lemma st1 : cell 969 1 = pat true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cell_succ, st0]
  exact step_pat 969 false true [(0, 0)] [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a273850 in
lemma st2 : cell 969 2 = pat true [(-1, -1), (-1, 1), (1, -1), (1, 1)] := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, cell_succ, st1]
  exact step_pat 969 true true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] [(-1, -1), (-1, 1), (1, -1), (1, 1)] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a273850 in
lemma st3 : cell 969 3 = pat true [(-1, 0), (0, -1), (0, 1), (1, 0)] := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, cell_succ, st2]
  exact step_pat 969 true true [(-1, -1), (-1, 1), (1, -1), (1, 1)] [(-1, 0), (0, -1), (0, 1), (1, 0)] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a273850 in
lemma st4 : cell 969 4 = pat true [(-1, -1), (-1, 1), (0, 0), (1, -1), (1, 1)] := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, cell_succ, st3]
  exact step_pat 969 true true [(-1, 0), (0, -1), (0, 1), (1, 0)] [(-1, -1), (-1, 1), (0, 0), (1, -1), (1, 1)] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a273850 in
lemma st5 : cell 969 5 = pat true [] := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, cell_succ, st4]
  exact step_pat 969 true true [(-1, -1), (-1, 1), (0, 0), (1, -1), (1, 1)] [] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a273850 in
lemma st6 : cell 969 6 = pat true [] := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, cell_succ, st5]
  exact step_pat 969 true true [] [] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a273850 in
lemma st7 : cell 969 7 = pat true [] := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, cell_succ, st6]
  exact step_pat 969 true true [] [] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

lemma stepAB : nxt 969 (pat true []) = pat true [] :=
  step_pat 969 true true [] [] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

lemma stepBA : nxt 969 (pat true []) = pat true [] :=
  step_pat 969 true true [] [] (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a273850 in
lemma stP (m : ℕ) : cell 969 (6 + 2 * m) = pat true [] ∧
    cell 969 (6 + 2 * m + 1) = pat true [] := by
  induction m with
  | zero => exact ⟨st6, st7⟩
  | succ k ih =>
    have h1 : cell 969 (6 + 2 * (k + 1)) = pat true [] := by
      rw [show 6 + 2 * (k + 1) = (6 + 2 * k + 1) + 1 from by ring, cell_succ, ih.2]
      exact stepBA
    refine ⟨h1, ?_⟩
    rw [cell_succ, h1]
    exact stepAB

open OMA.S_oeis_a273850 in
lemma oc0 : onCount 969 0 = 1 :=
  onCount_false 969 0 _ 1 rfl (by decide) (by decide) st0

open OMA.S_oeis_a273850 in
lemma oc1 : onCount 969 1 = 4 := by
  have h := onCount_true 969 1 _ 5 rfl (by decide) (by decide) st1
  omega

open OMA.S_oeis_a273850 in
lemma oc2 : onCount 969 2 = 21 := by
  have h := onCount_true 969 2 _ 4 rfl (by decide) (by decide) st2
  omega

open OMA.S_oeis_a273850 in
lemma oc3 : onCount 969 3 = 45 := by
  have h := onCount_true 969 3 _ 4 rfl (by decide) (by decide) st3
  omega

open OMA.S_oeis_a273850 in
lemma oc4 : onCount 969 4 = 76 := by
  have h := onCount_true 969 4 _ 5 rfl (by decide) (by decide) st4
  omega

open OMA.S_oeis_a273850 in
lemma oc5 : onCount 969 5 = 121 := by
  have h := onCount_true 969 5 _ 0 rfl (by decide) (by decide) st5
  omega

open OMA.S_oeis_a273850 in
lemma oc6 : onCount 969 6 = 169 := by
  have h := onCount_true 969 6 _ 0 rfl (by decide) (by decide) st6
  omega

open OMA.S_oeis_a273850 in
lemma oc7 : onCount 969 7 = 225 := by
  have h := onCount_true 969 7 _ 0 rfl (by decide) (by decide) st7
  omega

lemma hLE : inBox [] := by unfold inBox; decide

open OMA.S_oeis_a273850 in
lemma ocE (m : ℕ) : (onCount 969 (6 + 2 * m) : ℤ) = (2 * (6 + 2 * (m : ℤ)) + 1) ^ 2 - 0 := by
  have h := onCount_true 969 (6 + 2 * m) _ 0 rfl (by decide) (fun p hp => by have h := hLE p hp; omega) (stP m).1
  have h' : ((onCount 969 (6 + 2 * m) : ℕ) : ℤ) + 0 = (2 * (6 + 2 * (m : ℤ)) + 1) ^ 2 := by exact_mod_cast h
  linarith

lemma hLO : inBox [] := by unfold inBox; decide

open OMA.S_oeis_a273850 in
lemma ocO (m : ℕ) : (onCount 969 (6 + 2 * m + 1) : ℤ) = (2 * (6 + 2 * (m : ℤ) + 1) + 1) ^ 2 - 0 := by
  have h := onCount_true 969 (6 + 2 * m + 1) _ 0 rfl (by decide) (fun p hp => by have h := hLO p hp; omega) (stP m).2
  have h' : ((onCount 969 (6 + 2 * m + 1) : ℕ) : ℤ) + 0 = (2 * (6 + 2 * (m : ℤ) + 1) + 1) ^ 2 := by exact_mod_cast h
  linarith

open OMA.S_oeis_a273850 in
lemma oc_eq (n : ℕ) (hn : 6 ≤ n) : (onCount 969 n : ℚ) = ((1 : ℚ) + (4 : ℚ) * (n : ℚ) + (4 : ℚ) * (n : ℚ) ^ 2) + (-1 : ℚ) ^ n * ((0 : ℚ)) := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 6 + 2 * m ∨ n = 6 + 2 * m + 1 := ⟨(n - 6) / 2, by omega⟩
  · have hs : (-1 : ℚ) ^ (6 + 2 * m) = 1 := Even.neg_one_pow ⟨3 + m, by ring⟩
    have h := ocE m
    have h' : ((onCount 969 (6 + 2 * m) : ℕ) : ℚ) = (((onCount 969 (6 + 2 * m) : ℕ) : ℤ) : ℚ) := by norm_cast
    rw [h', h, hs]
    push_cast
    ring
  · have hs : (-1 : ℚ) ^ (6 + 2 * m + 1) = -1 := Odd.neg_one_pow ⟨3 + m, by ring⟩
    have h := ocO m
    have h' : ((onCount 969 (6 + 2 * m + 1) : ℕ) : ℚ) = (((onCount 969 (6 + 2 * m + 1) : ℕ) : ℤ) : ℚ) := by norm_cast
    rw [h', h, hs]
    push_cast
    ring

open OMA.S_oeis_a273850 in
lemma a_eq (n : ℕ) (hn : 6 ≤ n) : (a n : ℚ) = ((8 : ℚ) + (8 : ℚ) * (n : ℚ)) + (-1 : ℚ) ^ n * ((0 : ℚ)) := by
  unfold a
  push_cast
  rw [oc_eq n hn, oc_eq (n + 1) (by omega), pow_succ]
  push_cast
  ring

open OMA.S_oeis_a273850 in
lemma av0 : (a 0 : ℚ) = 3 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7]

open OMA.S_oeis_a273850 in
lemma av1 : (a 1 : ℚ) = 17 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7]

open OMA.S_oeis_a273850 in
lemma av2 : (a 2 : ℚ) = 24 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7]

open OMA.S_oeis_a273850 in
lemma av3 : (a 3 : ℚ) = 31 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7]

open OMA.S_oeis_a273850 in
lemma av4 : (a 4 : ℚ) = 45 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7]

open OMA.S_oeis_a273850 in
lemma av5 : (a 5 : ℚ) = 48 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7]

open OMA.S_oeis_a273850 in
lemma av6 : (a 6 : ℚ) = 56 := by
  rw [a_eq 6 (by norm_num)]
  norm_num

open OMA.S_oeis_a273850 in
lemma av7 : (a 7 : ℚ) = 64 := by
  rw [a_eq 7 (by norm_num)]
  norm_num

open OMA.S_oeis_a273850 in
lemma av8 : (a 8 : ℚ) = 72 := by
  rw [a_eq 8 (by norm_num)]
  norm_num

end CAOEISA273850Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a273850 CAOEISA273850Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a273850.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n
      · rw [av5]
        norm_num
    · rw [a_eq n h]
      ring
  · intro n hn
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n
      · norm_num [av5, av6, av7]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      rw [show m + 8 - 1 = m + 7 from by omega, show m + 8 - 2 = m + 6 from by omega]
      rw [a_eq (m + 8) (by omega), a_eq (m + 7) (by omega), a_eq (m + 6) (by omega)]
      push_cast
      ring
  · have hD : (((1 - PowerSeries.X) ^ 2) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-2) * PowerSeries.X ^ 1 + PowerSeries.C 1 * PowerSeries.X ^ 2 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : ((3 + 11 * PowerSeries.X - 7 * PowerSeries.X ^ 2 + 7 * PowerSeries.X ^ 4 - 11 * PowerSeries.X ^ 5 + 5 * PowerSeries.X ^ 6) : PowerSeries ℚ) =
        PowerSeries.C 3 * PowerSeries.X ^ 0 + PowerSeries.C 11 * PowerSeries.X ^ 1 + PowerSeries.C (-7) * PowerSeries.X ^ 2 + PowerSeries.C 7 * PowerSeries.X ^ 4 + PowerSeries.C (-11) * PowerSeries.X ^ 5 + PowerSeries.C 5 * PowerSeries.X ^ 6 := by
      simp only [map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n
      · norm_num [av0]
      · norm_num [av0, av1]
      · norm_num [av0, av1, av2]
      · norm_num [av1, av2, av3]
      · norm_num [av2, av3, av4]
      · norm_num [av3, av4, av5]
      · norm_num [av4, av5, av6]
      · norm_num [av5, av6, av7]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      rw [if_pos (show 0 ≤ m + 8 from by omega), if_pos (show 1 ≤ m + 8 from by omega), if_pos (show 2 ≤ m + 8 from by omega)]
      rw [if_neg (show ¬ (m + 8 = 0) from by omega), if_neg (show ¬ (m + 8 = 1) from by omega), if_neg (show ¬ (m + 8 = 2) from by omega), if_neg (show ¬ (m + 8 = 4) from by omega), if_neg (show ¬ (m + 8 = 5) from by omega), if_neg (show ¬ (m + 8 = 6) from by omega)]
      rw [show m + 8 - 0 = m + 8 from by omega, show m + 8 - 1 = m + 7 from by omega, show m + 8 - 2 = m + 6 from by omega]
      rw [a_eq (m + 8) (by omega), a_eq (m + 7) (by omega), a_eq (m + 6) (by omega)]
      push_cast
      ring
