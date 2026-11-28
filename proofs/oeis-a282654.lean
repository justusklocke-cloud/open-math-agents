import OMAStatements.S_oeis_a282654
import Mathlib

namespace A282654Aux

def st (b : Bool) (L : List (ℤ × ℤ)) : ℤ → ℤ → Bool := fun x y => xor b (decide ((x, y) ∈ L))

def stp (code : ℕ) (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun x y =>
  code.testBit ((g x y).toNat + 2 * ((g (x - 1) y).toNat + (g (x + 1) y).toNat +
    (g x (y - 1)).toNat + (g x (y + 1)).toNat))

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
    rw [st_far b r L hL x y (by omega), st_far b r L hL (x - 1) y (by omega),
      st_far b r L hL (x + 1) y (by omega), st_far b r L hL x (y - 1) (by omega),
      st_far b r L hL x (y + 1) (by omega)]
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
    (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      ((st b L ((i : ℤ) - t) ((j : ℤ) - t)).toNat : ℤ)) =
      if b then (2 * (t : ℤ) + 1) ^ 2 - (L.length : ℤ) else (L.length : ℤ) := by
  have hc := count_fin t L hnd hbox
  have key : ∀ i j : ℕ, ((st b L ((i : ℤ) - t) ((j : ℤ) - t)).toNat : ℤ) =
      if b then 1 - (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then (1 : ℤ) else 0)
      else (if (((i : ℤ) - t, (j : ℤ) - t) ∈ L) then (1 : ℤ) else 0) := by
    intro i j
    unfold st
    by_cases h : (((i : ℤ) - t, (j : ℤ) - t) ∈ L) <;> cases b <;> simp [h]
  simp only [key]
  cases b
  · simpa using hc
  · simp only [if_true, Finset.sum_sub_distrib, hc]
    simp
    ring

open OMA.S_oeis_a282654 in
lemma state_zero (code : ℕ) : state code 0 = st false [(0, 0)] := by
  funext x y
  simp [state, st]

open OMA.S_oeis_a282654 in
lemma state_succ (code t : ℕ) : state code (t + 1) = stp code (state code t) := rfl


open OMA.S_oeis_a282654 in
lemma s0 : state 491 0 = st false [(0, 0)] := state_zero 491

set_option maxRecDepth 100000 in
lemma step0 : stp 491 (st false [(0, 0)]) = st true [(-1, 0), (0, -1), (0, 1), (1, 0)] :=
  step_st 491 1 false true _ _ (by unfold inBox; decide +kernel) (by unfold inBox; decide +kernel) (by decide) (by decide +kernel)

open OMA.S_oeis_a282654 in
lemma s1 : state 491 1 = st true [(-1, 0), (0, -1), (0, 1), (1, 0)] := by
  rw [state_succ, s0]
  exact step0

set_option maxRecDepth 100000 in
lemma step1 : stp 491 (st true [(-1, 0), (0, -1), (0, 1), (1, 0)]) = st false [(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (2, 0)] :=
  step_st 491 2 true false _ _ (by unfold inBox; decide +kernel) (by unfold inBox; decide +kernel) (by decide) (by decide +kernel)

open OMA.S_oeis_a282654 in
lemma s2 : state 491 2 = st false [(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (2, 0)] := by
  rw [state_succ, s1]
  exact step1

set_option maxRecDepth 100000 in
lemma step2 : stp 491 (st false [(-2, 0), (-1, -1), (-1, 0), (-1, 1), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (1, -1), (1, 0), (1, 1), (2, 0)]) = st true [(-3, 0), (-2, -1), (-2, 1), (-1, -2), (-1, 0), (-1, 2), (0, -3), (0, -1), (0, 0), (0, 1), (0, 3), (1, -2), (1, 0), (1, 2), (2, -1), (2, 1), (3, 0)] :=
  step_st 491 3 false true _ _ (by unfold inBox; decide +kernel) (by unfold inBox; decide +kernel) (by decide) (by decide +kernel)

open OMA.S_oeis_a282654 in
lemma s3 : state 491 3 = st true [(-3, 0), (-2, -1), (-2, 1), (-1, -2), (-1, 0), (-1, 2), (0, -3), (0, -1), (0, 0), (0, 1), (0, 3), (1, -2), (1, 0), (1, 2), (2, -1), (2, 1), (3, 0)] := by
  rw [state_succ, s2]
  exact step2

set_option maxRecDepth 100000 in
lemma step3 : stp 491 (st true [(-3, 0), (-2, -1), (-2, 1), (-1, -2), (-1, 0), (-1, 2), (0, -3), (0, -1), (0, 0), (0, 1), (0, 3), (1, -2), (1, 0), (1, 2), (2, -1), (2, 1), (3, 0)]) = st false [(-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (4, 0)] :=
  step_st 491 4 true false _ _ (by unfold inBox; decide +kernel) (by unfold inBox; decide +kernel) (by decide) (by decide +kernel)

open OMA.S_oeis_a282654 in
lemma s4 : state 491 4 = st false [(-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (4, 0)] := by
  rw [state_succ, s3]
  exact step3

set_option maxRecDepth 100000 in
lemma step4 : stp 491 (st false [(-4, 0), (-3, -1), (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-2, 2), (-1, -3), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 3), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, -3), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 3), (2, -2), (2, -1), (2, 0), (2, 1), (2, 2), (3, -1), (3, 0), (3, 1), (4, 0)]) = st true [(-5, 0), (-4, -1), (-4, 1), (-3, -2), (-3, 0), (-3, 2), (-2, -3), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-1, -4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 4), (0, -5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (1, -4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 4), (2, -3), (2, -1), (2, 0), (2, 1), (2, 3), (3, -2), (3, 0), (3, 2), (4, -1), (4, 1), (5, 0)] :=
  step_st 491 5 false true _ _ (by unfold inBox; decide +kernel) (by unfold inBox; decide +kernel) (by decide) (by decide +kernel)

open OMA.S_oeis_a282654 in
lemma s5 : state 491 5 = st true [(-5, 0), (-4, -1), (-4, 1), (-3, -2), (-3, 0), (-3, 2), (-2, -3), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-1, -4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 4), (0, -5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (1, -4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 4), (2, -3), (2, -1), (2, 0), (2, 1), (2, 3), (3, -2), (3, 0), (3, 2), (4, -1), (4, 1), (5, 0)] := by
  rw [state_succ, s4]
  exact step4

set_option maxRecDepth 100000 in
lemma step5 : stp 491 (st true [(-5, 0), (-4, -1), (-4, 1), (-3, -2), (-3, 0), (-3, 2), (-2, -3), (-2, -1), (-2, 0), (-2, 1), (-2, 3), (-1, -4), (-1, -2), (-1, -1), (-1, 0), (-1, 1), (-1, 2), (-1, 4), (0, -5), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 5), (1, -4), (1, -2), (1, -1), (1, 0), (1, 1), (1, 2), (1, 4), (2, -3), (2, -1), (2, 0), (2, 1), (2, 3), (3, -2), (3, 0), (3, 2), (4, -1), (4, 1), (5, 0)]) = st false [(-6, 0), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -4), (-2, -3), (-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (-1, 5), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (2, -4), (2, -3), (2, -2), (2, 0), (2, 2), (2, 3), (2, 4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1), (5, 0), (5, 1), (6, 0)] :=
  step_st 491 6 true false _ _ (by unfold inBox; decide +kernel) (by unfold inBox; decide +kernel) (by decide) (by decide +kernel)

open OMA.S_oeis_a282654 in
lemma s6 : state 491 6 = st false [(-6, 0), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -4), (-2, -3), (-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (-1, 5), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (2, -4), (2, -3), (2, -2), (2, 0), (2, 2), (2, 3), (2, 4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1), (5, 0), (5, 1), (6, 0)] := by
  rw [state_succ, s5]
  exact step5

set_option maxRecDepth 100000 in
lemma step6 : stp 491 (st false [(-6, 0), (-5, -1), (-5, 0), (-5, 1), (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -3), (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-3, 3), (-2, -4), (-2, -3), (-2, -2), (-2, 0), (-2, 2), (-2, 3), (-2, 4), (-1, -5), (-1, -4), (-1, -3), (-1, -1), (-1, 0), (-1, 1), (-1, 3), (-1, 4), (-1, 5), (0, -6), (0, -5), (0, -4), (0, -3), (0, -2), (0, -1), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, -5), (1, -4), (1, -3), (1, -1), (1, 0), (1, 1), (1, 3), (1, 4), (1, 5), (2, -4), (2, -3), (2, -2), (2, 0), (2, 2), (2, 3), (2, 4), (3, -3), (3, -2), (3, -1), (3, 0), (3, 1), (3, 2), (3, 3), (4, -2), (4, -1), (4, 0), (4, 1), (4, 2), (5, -1), (5, 0), (5, 1), (6, 0)]) = st true [(-7, 0), (-6, -1), (-6, 1), (-5, -2), (-5, 0), (-5, 2), (-4, -3), (-4, -1), (-4, 0), (-4, 1), (-4, 3), (-3, -4), (-3, -2), (-3, 0), (-3, 2), (-3, 4), (-2, -5), (-2, -3), (-2, 3), (-2, 5), (-1, -6), (-1, -4), (-1, 0), (-1, 4), (-1, 6), (0, -7), (0, -5), (0, -4), (0, -3), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (0, 7), (1, -6), (1, -4), (1, 0), (1, 4), (1, 6), (2, -5), (2, -3), (2, 3), (2, 5), (3, -4), (3, -2), (3, 0), (3, 2), (3, 4), (4, -3), (4, -1), (4, 0), (4, 1), (4, 3), (5, -2), (5, 0), (5, 2), (6, -1), (6, 1), (7, 0)] :=
  step_st 491 7 false true _ _ (by unfold inBox; decide +kernel) (by unfold inBox; decide +kernel) (by decide) (by decide +kernel)

open OMA.S_oeis_a282654 in
lemma s7 : state 491 7 = st true [(-7, 0), (-6, -1), (-6, 1), (-5, -2), (-5, 0), (-5, 2), (-4, -3), (-4, -1), (-4, 0), (-4, 1), (-4, 3), (-3, -4), (-3, -2), (-3, 0), (-3, 2), (-3, 4), (-2, -5), (-2, -3), (-2, 3), (-2, 5), (-1, -6), (-1, -4), (-1, 0), (-1, 4), (-1, 6), (0, -7), (0, -5), (0, -4), (0, -3), (0, -1), (0, 0), (0, 1), (0, 3), (0, 4), (0, 5), (0, 7), (1, -6), (1, -4), (1, 0), (1, 4), (1, 6), (2, -5), (2, -3), (2, 3), (2, 5), (3, -4), (3, -2), (3, 0), (3, 2), (3, 4), (4, -3), (4, -1), (4, 0), (4, 1), (4, 3), (5, -2), (5, 0), (5, 2), (6, -1), (6, 1), (7, 0)] := by
  rw [state_succ, s6]
  exact step6

set_option maxRecDepth 100000 in
open OMA.S_oeis_a282654 in
lemma dv1 : a 1 = 1 := by
  unfold a digits
  rw [s1]
  decide +kernel

set_option maxRecDepth 100000 in
open OMA.S_oeis_a282654 in
lemma dv3 : a 3 = 4 := by
  unfold a digits
  rw [s3]
  decide +kernel

set_option maxRecDepth 100000 in
open OMA.S_oeis_a282654 in
lemma dv5 : a 5 = 16 := by
  unfold a digits
  rw [s5]
  decide +kernel

set_option maxRecDepth 100000 in
open OMA.S_oeis_a282654 in
lemma dv7 : a 7 = 68 := by
  unfold a digits
  rw [s7]
  decide +kernel

end A282654Aux

open OMA.S_oeis_a282654 A282654Aux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282654.main) := by
  intro h
  have h7 := h.1 7 (by norm_num)
  norm_num [dv1, dv3, dv5, dv7] at h7
