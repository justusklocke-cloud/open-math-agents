import OMAStatements.S_oeis_a271053
import Mathlib

namespace A271053Aux

def st (b : Bool) (L : List (ℤ × ℤ)) : ℤ → ℤ → Bool := fun x y => xor b (decide ((x, y) ∈ L))

def stp (code : ℕ) (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun i j =>
  code.testBit ((g i j).toNat + 2 * ((g (i + 1) j).toNat + (g (i - 1) j).toNat +
    (g i (j + 1)).toNat + (g i (j - 1)).toNat))

def inBox (r : ℤ) (L : List (ℤ × ℤ)) : Prop :=
  ∀ p ∈ L, -r ≤ p.1 ∧ p.1 ≤ r ∧ -r ≤ p.2 ∧ p.2 ≤ r

def rng (r : ℕ) : List ℤ := (List.range (2 * r + 3)).map (fun k : ℕ => (k : ℤ) - ((r : ℤ) + 1))

lemma mem_rng (r : ℕ) (x : ℤ) (h1 : -(r : ℤ) - 1 ≤ x) (h2 : x ≤ r + 1) : x ∈ rng r := by
  unfold rng
  rw [List.mem_map]
  refine ⟨(x + (r + 1)).toNat, ?_, ?_⟩
  · rw [List.mem_range]
    omega
  · have h : (((x + (r + 1)).toNat : ℕ) : ℤ) = x + (r + 1) := Int.toNat_of_nonneg (by omega)
    omega

lemma inBox_mono (r t : ℤ) (h : r ≤ t) (L : List (ℤ × ℤ)) (hL : inBox r L) : inBox t L := by
  intro p hp
  have := hL p hp
  omega

lemma st_far (b : Bool) (r : ℤ) (L : List (ℤ × ℤ)) (hL : inBox r L) (u v : ℤ)
    (h : ¬(-r ≤ u ∧ u ≤ r ∧ -r ≤ v ∧ v ≤ r)) : st b L u v = b := by
  unfold st
  have hm : (u, v) ∉ L := fun hm => h (hL _ hm)
  simp [hm]

lemma step_st (code : ℕ) (r : ℕ) (b b' : Bool) (L L' : List (ℤ × ℤ))
    (hL : inBox r L) (hL' : inBox r L')
    (hr : code.testBit (b.toNat + 2 * (b.toNat + b.toNat + b.toNat + b.toNat)) = b')
    (hbox : ∀ x ∈ rng r, ∀ y ∈ rng r, stp code (st b L) x y = st b' L' x y) :
    stp code (st b L) = st b' L' := by
  funext x y
  by_cases h : (-(r : ℤ) - 1 ≤ x ∧ x ≤ r + 1) ∧ (-(r : ℤ) - 1 ≤ y ∧ y ≤ r + 1)
  · exact hbox x (mem_rng r x h.1.1 h.1.2) y (mem_rng r y h.2.1 h.2.2)
  · rw [st_far b' r L' hL' x y (by omega)]
    unfold stp
    rw [st_far b r L hL x y (by omega), st_far b r L hL (x + 1) y (by omega),
      st_far b r L hL (x - 1) y (by omega), st_far b r L hL x (y + 1) (by omega),
      st_far b r L hL x (y - 1) (by omega)]
    exact hr

lemma count_one (t : ℕ) (p : ℤ × ℤ)
    (hp : -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t) :
    (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      if (((i : ℤ) - t, (j : ℤ) - t) = p) then (1 : ℤ) else 0) = 1 := by
  obtain ⟨px, py⟩ := p
  have hx1 : -(t : ℤ) ≤ px := hp.1
  have hx2 : px ≤ t := hp.2.1
  have hy1 : -(t : ℤ) ≤ py := hp.2.2.1
  have hy2 : py ≤ t := hp.2.2.2
  have h1 : (((px + t).toNat : ℕ) : ℤ) = px + t := Int.toNat_of_nonneg (by omega)
  have h2 : (((py + t).toNat : ℕ) : ℤ) = py + t := Int.toNat_of_nonneg (by omega)
  rw [Finset.sum_eq_single (px + t).toNat]
  · rw [Finset.sum_eq_single (py + t).toNat]
    · rw [if_pos]
      rw [h1, h2]
      simp
    · intro j _ hj
      rw [if_neg]
      intro h
      apply hj
      have := (Prod.mk.inj h).2
      omega
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro h
    apply hi
    have := (Prod.mk.inj h).1
    omega
  · intro h
    exfalso
    apply h
    rw [Finset.mem_range]
    omega

lemma count_fin (t : ℕ) (L : List (ℤ × ℤ)) (hnd : L.Nodup) (hbox : inBox t L) :
    (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then (1 : ℤ) else 0) = L.length := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp : p ∉ L := (List.nodup_cons.mp hnd).1
    have h1 := ih (List.nodup_cons.mp hnd).2 (fun q hq => hbox q (List.mem_cons_of_mem _ hq))
    have h2 := count_one t p (hbox p List.mem_cons_self)
    have hsplit : (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
        if (((i : ℤ) - t, (j : ℤ) - t) ∈ p :: L) then (1 : ℤ) else 0) =
        (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
          if (((i : ℤ) - t, (j : ℤ) - t) = p) then (1 : ℤ) else 0) +
        (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
          if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then (1 : ℤ) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hq : ((i : ℤ) - t, (j : ℤ) - t) = p
      · have hq' : ((i : ℤ) - t, (j : ℤ) - t) ∉ L := hq ▸ hp
        rw [if_pos (hq ▸ List.mem_cons_self), if_neg hq', if_pos hq]
        norm_num
      · by_cases hm : ((i : ℤ) - t, (j : ℤ) - t) ∈ L
        · rw [if_pos (List.mem_cons_of_mem _ hm), if_pos hm, if_neg hq]
          norm_num
        · have hm' : ((i : ℤ) - t, (j : ℤ) - t) ∉ p :: L := by
            intro h
            rcases List.mem_cons.mp h with h | h
            · exact hq h
            · exact hm h
          rw [if_neg hm', if_neg hm, if_neg hq]
          norm_num
    rw [hsplit, h1, h2, List.length_cons]
    push_cast
    ring

lemma count_st (t : ℕ) (b : Bool) (L : List (ℤ × ℤ)) (hnd : L.Nodup) (hbox : inBox t L) :
    ((∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      if st b L ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0 : ℕ) : ℤ) =
      if b then (2 * (t : ℤ) + 1) ^ 2 - (L.length : ℤ) else (L.length : ℤ) := by
  have hc := count_fin t L hnd hbox
  have key : ∀ i j : ℕ, (if st b L ((i : ℤ) - t) ((j : ℤ) - t) then (1 : ℤ) else 0) =
      if b then 1 - (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then (1 : ℤ) else 0)
      else (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then (1 : ℤ) else 0) := by
    intro i j
    unfold st
    by_cases h : (((i : ℤ) - t, (j : ℤ) - t) ∈ L) <;> cases b <;> simp [h]
  push_cast
  simp only [key]
  cases b
  · simpa using hc
  · simp only [if_true, Finset.sum_sub_distrib, hc]
    simp
    ring

open OMA.S_oeis_a271053 in
lemma cell_zero (code : ℕ) : cell code 0 = st false [(0, 0)] := by
  funext i j
  simp [cell, st]

open OMA.S_oeis_a271053 in
lemma cell_succ (code t : ℕ) : cell code (t + 1) = stp code (cell code t) := rfl

open OMA.S_oeis_a271053 in
lemma on_of_state (code t : ℕ) (b : Bool) (L : List (ℤ × ℤ)) (hs : cell code t = st b L)
    (hnd : L.Nodup) (hbox : inBox t L) :
    (onCount code t : ℤ) = if b then (2 * (t : ℤ) + 1) ^ 2 - (L.length : ℤ) else (L.length : ℤ) := by
  unfold onCount
  rw [hs]
  exact count_st t b L hnd hbox


lemma step0 : stp 253 (st false [(0, 0)]) = st true [(0, 0)] :=
  step_st 253 2 false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

lemma step1 : stp 253 (st true [(0, 0)]) = st false [(-1, 0), (0, -1), (0, 1), (1, 0)] :=
  step_st 253 2 true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

lemma step2 : stp 253 (st false [(-1, 0), (0, -1), (0, 1), (1, 0)]) = st true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] :=
  step_st 253 2 false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

lemma stepAB : stp 253 (st true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)]) = st false [(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (2, 0)] :=
  step_st 253 2 true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

lemma stepBA : stp 253 (st false [(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (2, 0)]) = st true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] :=
  step_st 253 2 false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a271053 in
lemma s0 : cell 253 0 = st false [(0, 0)] := cell_zero 253

open OMA.S_oeis_a271053 in
lemma s1 : cell 253 1 = st true [(0, 0)] := by
  rw [cell_succ, s0]
  exact step0

open OMA.S_oeis_a271053 in
lemma s2 : cell 253 2 = st false [(-1, 0), (0, -1), (0, 1), (1, 0)] := by
  rw [cell_succ, s1]
  exact step1

open OMA.S_oeis_a271053 in
lemma s3 : cell 253 3 = st true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] := by
  rw [cell_succ, s2]
  exact step2

open OMA.S_oeis_a271053 in
lemma s4 : cell 253 4 = st false [(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (2, 0)] := by
  rw [cell_succ, s3]
  exact stepAB

open OMA.S_oeis_a271053 in
lemma per (m : ℕ) : cell 253 (3 + 2 * m) = st true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] ∧ cell 253 (3 + 2 * m + 1) = st false [(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (2, 0)] := by
  induction m with
  | zero => exact ⟨s3, s4⟩
  | succ k ih =>
    have h1 : cell 253 (3 + 2 * (k + 1)) = st true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] := by
      have e : 3 + 2 * (k + 1) = (3 + 2 * k + 1) + 1 := by ring
      rw [e, cell_succ, ih.2]
      exact stepBA
    refine ⟨h1, ?_⟩
    rw [cell_succ, h1]
    exact stepAB

open OMA.S_oeis_a271053 in
lemma onO (t : ℕ) (h0 : 3 ≤ t) (hp : t % 2 = 1) : (onCount 253 t : ℤ) = (2 * (t : ℤ) + 1) ^ 2 - 5 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 3 + 2 * m := ⟨(t - 3) / 2, by omega⟩
  rw [on_of_state 253 (3 + 2 * m) true [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)] (per m).1 (by decide)
    (inBox_mono 1 _ (by omega) _ (by unfold inBox; decide))]
  simp

open OMA.S_oeis_a271053 in
lemma onE (t : ℕ) (h0 : 4 ≤ t) (hp : t % 2 = 0) : (onCount 253 t : ℤ) = 13 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 3 + 2 * m + 1 := ⟨(t - 4) / 2, by omega⟩
  rw [on_of_state 253 (3 + 2 * m + 1) false [(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (2, 0)] (per m).2 (by decide)
    (inBox_mono 2 _ (by omega) _ (by unfold inBox; decide))]
  simp

open OMA.S_oeis_a271053 in
lemma ov0 : (onCount 253 0 : ℤ) = 1 := by
  rw [on_of_state 253 0 false [(0, 0)] s0 (by decide) (by unfold inBox; decide)]
  simp

open OMA.S_oeis_a271053 in
lemma ov1 : (onCount 253 1 : ℤ) = 8 := by
  rw [on_of_state 253 1 true [(0, 0)] s1 (by decide) (by unfold inBox; decide)]
  simp

open OMA.S_oeis_a271053 in
lemma ov2 : (onCount 253 2 : ℤ) = 4 := by
  rw [on_of_state 253 2 false [(-1, 0), (0, -1), (0, 1), (1, 0)] s2 (by decide) (by unfold inBox; decide)]
  simp

open OMA.S_oeis_a271053 in
lemma ov3 : (onCount 253 3 : ℤ) = 44 :=
  (onO 3 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a271053 in
lemma ov4 : (onCount 253 4 : ℤ) = 13 :=
  (onE 4 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a271053 in
lemma ov5 : (onCount 253 5 : ℤ) = 116 :=
  (onO 5 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a271053 in
lemma ov6 : (onCount 253 6 : ℤ) = 13 :=
  (onE 6 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a271053 in
lemma ov7 : (onCount 253 7 : ℤ) = 220 :=
  (onO 7 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a271053 in
lemma ov8 : (onCount 253 8 : ℤ) = 13 :=
  (onE 8 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a271053 in
lemma ov9 : (onCount 253 9 : ℤ) = 356 :=
  (onO 9 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a271053 in
lemma ov10 : (onCount 253 10 : ℤ) = 13 :=
  (onE 10 (by norm_num) (by norm_num)).trans (by norm_num)

open OMA.S_oeis_a271053 in
lemma aE (n : ℕ) (h0 : 4 ≤ n) (hp : n % 2 = 0) : (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (4 : ℚ) * (n : ℚ) ^ 2 + (12 : ℚ) * (n : ℚ) + (-9 : ℚ) := by
  unfold a
  rw [onO (n + 1) (by omega) (by omega), onE n (by omega) hp]
  push_cast
  ring

open OMA.S_oeis_a271053 in
lemma aO (n : ℕ) (h0 : 3 ≤ n) (hp : n % 2 = 1) : (a n : ℚ) = (0 : ℚ) * (n : ℚ) ^ 3 + (-4 : ℚ) * (n : ℚ) ^ 2 + (-4 : ℚ) * (n : ℚ) + (17 : ℚ) := by
  unfold a
  rw [onE (n + 1) (by omega) (by omega), onO n (by omega) hp]
  push_cast
  ring

open OMA.S_oeis_a271053 in
lemma av0 : (a 0 : ℚ) = 7 := by
  unfold a
  rw [ov1, ov0]
  norm_num

open OMA.S_oeis_a271053 in
lemma av1 : (a 1 : ℚ) = -4 := by
  unfold a
  rw [ov2, ov1]
  norm_num

open OMA.S_oeis_a271053 in
lemma av2 : (a 2 : ℚ) = 40 := by
  unfold a
  rw [ov3, ov2]
  norm_num

open OMA.S_oeis_a271053 in
lemma av3 : (a 3 : ℚ) = -31 := by
  unfold a
  rw [ov4, ov3]
  norm_num

open OMA.S_oeis_a271053 in
lemma av4 : (a 4 : ℚ) = 103 := by
  unfold a
  rw [ov5, ov4]
  norm_num

open OMA.S_oeis_a271053 in
lemma av5 : (a 5 : ℚ) = -103 := by
  unfold a
  rw [ov6, ov5]
  norm_num

open OMA.S_oeis_a271053 in
lemma av6 : (a 6 : ℚ) = 207 := by
  unfold a
  rw [ov7, ov6]
  norm_num

open OMA.S_oeis_a271053 in
lemma av7 : (a 7 : ℚ) = -207 := by
  unfold a
  rw [ov8, ov7]
  norm_num

open OMA.S_oeis_a271053 in
lemma av8 : (a 8 : ℚ) = 343 := by
  unfold a
  rw [ov9, ov8]
  norm_num

open OMA.S_oeis_a271053 in
lemma rec_gen (m : ℕ) : (1 : ℚ) * (a (m + 9) : ℚ) + (1 : ℚ) * (a (m + 8) : ℚ) + (-2 : ℚ) * (a (m + 7) : ℚ) + (-2 : ℚ) * (a (m + 6) : ℚ) + (1 : ℚ) * (a (m + 5) : ℚ) + (1 : ℚ) * (a (m + 4) : ℚ) = 0 := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · rw [aO (m + 9) (by omega) (by omega),
      aE (m + 8) (by omega) (by omega),
      aO (m + 7) (by omega) (by omega),
      aE (m + 6) (by omega) (by omega),
      aO (m + 5) (by omega) (by omega),
      aE (m + 4) (by omega) (by omega)]
    push_cast
    ring
  · rw [aE (m + 9) (by omega) (by omega),
      aO (m + 8) (by omega) (by omega),
      aE (m + 7) (by omega) (by omega),
      aO (m + 6) (by omega) (by omega),
      aE (m + 5) (by omega) (by omega),
      aO (m + 4) (by omega) (by omega)]
    push_cast
    ring

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A271053Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a271053 A271053Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a271053.main := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hD : (((1 - X) ^ 2 * (1 + X) ^ 3 : PowerSeries ℚ)) = C (1 : ℚ) * X ^ 0 + C (1 : ℚ) * X ^ 1 + C (-2 : ℚ) * X ^ 2 + C (-2 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 + C (1 : ℚ) * X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : (7 + 3 * X + 22 * X ^ 2 + 3 * X ^ 3 + 7 * X ^ 4 - 15 * X ^ 5 - 4 * X ^ 6 + 9 * X ^ 7 : PowerSeries ℚ) = C (7 : ℚ) * X ^ 0 + C (3 : ℚ) * X ^ 1 + C (22 : ℚ) * X ^ 2 + C (3 : ℚ) * X ^ 3 + C (7 : ℚ) * X ^ 4 + C (-15 : ℚ) * X ^ 5 + C (-4 : ℚ) * X ^ 6 + C (9 : ℚ) * X ^ 7 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 9 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3, av4, av5, av6, av7, av8]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      rw [if_pos (show 0 ≤ m + 9 by omega),
        if_pos (show 1 ≤ m + 9 by omega),
        if_pos (show 2 ≤ m + 9 by omega),
        if_pos (show 3 ≤ m + 9 by omega),
        if_pos (show 4 ≤ m + 9 by omega),
        if_pos (show 5 ≤ m + 9 by omega),
        if_neg (show ¬ (m + 9 = 0) by omega),
        if_neg (show ¬ (m + 9 = 1) by omega),
        if_neg (show ¬ (m + 9 = 2) by omega),
        if_neg (show ¬ (m + 9 = 3) by omega),
        if_neg (show ¬ (m + 9 = 4) by omega),
        if_neg (show ¬ (m + 9 = 5) by omega),
        if_neg (show ¬ (m + 9 = 6) by omega),
        if_neg (show ¬ (m + 9 = 7) by omega)]
      rw [show m + 9 - 1 = m + 8 from by omega,
        show m + 9 - 2 = m + 7 from by omega,
        show m + 9 - 3 = m + 6 from by omega,
        show m + 9 - 4 = m + 5 from by omega,
        show m + 9 - 5 = m + 4 from by omega]
      rw [show m + 9 - 0 = m + 9 from by omega]
      have hrec := rec_gen m
      linarith
  · intro n hn hpar
    rcases Nat.lt_or_ge n 4 with hs | hs
    · interval_cases n <;> first | (exfalso; revert hpar; decide) | norm_num [av0, av1, av2, av3, av4, av5, av6, av7, av8]
    · rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have h1 : (-1 : ℚ) ^ n = 1 := Even.neg_one_pow (Nat.even_iff.mpr h)
        rw [aE n (by omega) h]
        ring
      · exfalso
        obtain ⟨k, hk⟩ := hpar
        omega
  · intro n hn hpar
    have hs : 3 ≤ n := by omega
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · exfalso
      obtain ⟨k, hk⟩ := hpar
      omega
    · have h1 : (-1 : ℚ) ^ n = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr h)
      rw [aO n (by omega) h]
      ring
  · intro n hn
    rcases Nat.lt_or_ge n 9 with hs | hs
    · interval_cases n <;> norm_num [av0, av1, av2, av3, av4, av5, av6, av7, av8]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
      rw [show j + 5 - 1 = j + 4 from by omega, show j + 5 - 2 = j + 3 from by omega, show j + 5 - 3 = j + 2 from by omega, show j + 5 - 4 = j + 1 from by omega, show j + 5 - 5 = j from by omega]
      rcases Nat.mod_two_eq_zero_or_one j with h | h
      · rw [aO (j + 5) (by omega) (by omega),
          aE (j + 4) (by omega) (by omega),
          aO (j + 3) (by omega) (by omega),
          aE (j + 2) (by omega) (by omega),
          aO (j + 1) (by omega) (by omega),
          aE (j) (by omega) (by omega)]
        push_cast
        ring
      · rw [aE (j + 5) (by omega) (by omega),
          aO (j + 4) (by omega) (by omega),
          aE (j + 3) (by omega) (by omega),
          aO (j + 2) (by omega) (by omega),
          aE (j + 1) (by omega) (by omega),
          aO (j) (by omega) (by omega)]
        push_cast
        ring
