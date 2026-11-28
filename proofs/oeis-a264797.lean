import OMAStatements.S_oeis_a264797
import Mathlib

namespace A264797Aux

open OMA.S_oeis_a264797 in
lemma step_gen (code t : ℕ) (f g : ℤ → ℤ → Bool)
    (hf : ∀ i j, cell code t i j = f i j)
    (h : ∀ (i j : ℤ), g i j = code.testBit ((f i j).toNat + 2 * ((f (i + 1) j).toNat +
      (f (i - 1) j).toNat + (f i (j + 1)).toNat + (f i (j - 1)).toNat))) :
    ∀ i j, cell code (t + 1) i j = g i j := by
  intro i j
  show code.testBit ((cell code t i j).toNat + 2 * ((cell code t (i + 1) j).toNat +
      (cell code t (i - 1) j).toNat + (cell code t i (j + 1)).toNat +
      (cell code t i (j - 1)).toNat)) = g i j
  rw [hf, hf, hf, hf, hf]
  exact (h i j).symm

lemma win (g : ℤ → ℕ) (r : ℕ) (hg : ∀ x : ℤ, (x < -(r : ℤ) ∨ (r : ℤ) < x) → g x = 0) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * (r + m) + 1), g ((i : ℤ) - ((r + m : ℕ) : ℤ)) =
      ∑ i ∈ Finset.range (2 * r + 1), g ((i : ℤ) - (r : ℤ)) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (r + (k + 1)) + 1 = (2 * (r + k) + 1) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ', ← ih]
    have e1 : g (((2 * (r + k) + 1 + 1 : ℕ) : ℤ) - ((r + (k + 1) : ℕ) : ℤ)) = 0 :=
      hg _ (by push_cast; omega)
    have e2 : g (((0 : ℕ) : ℤ) - ((r + (k + 1) : ℕ) : ℤ)) = 0 := hg _ (by push_cast; omega)
    rw [e1, e2, add_zero, add_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    push_cast
    ring

lemma win2 (F : ℤ → ℤ → ℕ) (r : ℕ)
    (hF : ∀ x y : ℤ, (x < -(r : ℤ) ∨ (r : ℤ) < x ∨ y < -(r : ℤ) ∨ (r : ℤ) < y) → F x y = 0)
    (m : ℕ) :
    ∑ i ∈ Finset.range (2 * (r + m) + 1), ∑ j ∈ Finset.range (2 * (r + m) + 1),
        F ((i : ℤ) - ((r + m : ℕ) : ℤ)) ((j : ℤ) - ((r + m : ℕ) : ℤ)) =
      ∑ i ∈ Finset.range (2 * r + 1), ∑ j ∈ Finset.range (2 * r + 1),
        F ((i : ℤ) - (r : ℤ)) ((j : ℤ) - (r : ℤ)) := by
  have h1 : ∀ x : ℤ, ∑ j ∈ Finset.range (2 * (r + m) + 1), F x ((j : ℤ) - ((r + m : ℕ) : ℤ)) =
      ∑ j ∈ Finset.range (2 * r + 1), F x ((j : ℤ) - (r : ℤ)) := fun x =>
    win (F x) r (fun y hy => hF x y (by omega)) m
  simp only [h1]
  exact win (fun x => ∑ j ∈ Finset.range (2 * r + 1), F x ((j : ℤ) - (r : ℤ))) r
    (fun x hx => Finset.sum_eq_zero (fun j _ => hF x _ (by omega))) m

lemma compl2 (p : ℤ → ℤ → Bool) (t : ℕ) :
    (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0)) +
      (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 0 else 1)) =
      (2 * t + 1) * (2 * t + 1) := by
  rw [← Finset.sum_add_distrib]
  have h : ∀ i ∈ Finset.range (2 * t + 1),
      (∑ j ∈ Finset.range (2 * t + 1), (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0)) +
      (∑ j ∈ Finset.range (2 * t + 1), (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 0 else 1))
      = 2 * t + 1 := by
    intro i _
    rw [← Finset.sum_add_distrib]
    have h2 : ∀ j ∈ Finset.range (2 * t + 1),
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0) +
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 0 else 1) = 1 := by
      intro j _
      split_ifs <;> rfl
    rw [Finset.sum_congr rfl h2]
    simp
  rw [Finset.sum_congr rfl h]
  simp

/-- the value of a cell at distance `d = |i| + |j|` from the origin after `t` steps -/
def v (t d : ℕ) : Bool :=
  decide ((t % 2 = 0 ∧ d ≤ t ∧ d % 4 = t % 4) ∨
    (t % 2 = 1 ∧ d ≤ t ∧ d % 4 ≠ (t + 1) % 4))

def q (t : ℕ) (i j : ℤ) : Bool := v t (i.natAbs + j.natAbs)

set_option maxHeartbeats 1600000 in
lemma rad_gen (t d k1 k2 : ℕ)
    (hk : (k1 = 2 ∧ k2 = 2 ∧ 1 ≤ d) ∨ (k1 = 1 ∧ k2 = 3 ∧ 1 ≤ d) ∨ (k1 = 0 ∧ k2 = 4 ∧ d = 0)) :
    v (t + 1) d = Nat.testBit 342 ((v t d).toNat +
      2 * (k1 * (v t (d - 1)).toNat + k2 * (v t (d + 1)).toNat)) := by
  rcases hk with ⟨rfl, rfl, hd⟩ | ⟨rfl, rfl, hd⟩ | ⟨rfl, rfl, hd⟩ <;>
  cases h0 : v t d <;> cases h1 : v t (d - 1) <;> cases h2 : v t (d + 1) <;>
  simp only [v, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
    Nat.testBit_eq_decide_div_mod_eq] at h0 h1 h2 ⊢ <;>
  norm_num <;> omega

lemma tr_q (t : ℕ) (i j : ℤ) : q (t + 1) i j = Nat.testBit 342 ((q t i j).toNat +
    2 * ((q t (i + 1) j).toNat + (q t (i - 1) j).toNat + (q t i (j + 1)).toNat +
      (q t i (j - 1)).toNat)) := by
  unfold q
  rcases lt_trichotomy i 0 with hi | hi | hi <;> rcases lt_trichotomy j 0 with hj | hj | hj
  · have e1 : (i + 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) - 1 := by omega
    have e2 : (i - 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e3 : i.natAbs + (j + 1).natAbs = (i.natAbs + j.natAbs) - 1 := by omega
    have e4 : i.natAbs + (j - 1).natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    rw [e1, e2, e3, e4, rad_gen t (i.natAbs + j.natAbs) 2 2 (by omega)]
    congr 1
    ring
  · have e1 : (i + 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) - 1 := by omega
    have e2 : (i - 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e3 : i.natAbs + (j + 1).natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e4 : i.natAbs + (j - 1).natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    rw [e1, e2, e3, e4, rad_gen t (i.natAbs + j.natAbs) 1 3 (by omega)]
    congr 1
    ring
  · have e1 : (i + 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) - 1 := by omega
    have e2 : (i - 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e3 : i.natAbs + (j + 1).natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e4 : i.natAbs + (j - 1).natAbs = (i.natAbs + j.natAbs) - 1 := by omega
    rw [e1, e2, e3, e4, rad_gen t (i.natAbs + j.natAbs) 2 2 (by omega)]
    congr 1
    ring
  · have e1 : (i + 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e2 : (i - 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e3 : i.natAbs + (j + 1).natAbs = (i.natAbs + j.natAbs) - 1 := by omega
    have e4 : i.natAbs + (j - 1).natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    rw [e1, e2, e3, e4, rad_gen t (i.natAbs + j.natAbs) 1 3 (by omega)]
    congr 1
    ring
  · have e1 : (i + 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e2 : (i - 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e3 : i.natAbs + (j + 1).natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e4 : i.natAbs + (j - 1).natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    rw [e1, e2, e3, e4, rad_gen t (i.natAbs + j.natAbs) 0 4 (by omega)]
    congr 1
    ring
  · have e1 : (i + 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e2 : (i - 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e3 : i.natAbs + (j + 1).natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e4 : i.natAbs + (j - 1).natAbs = (i.natAbs + j.natAbs) - 1 := by omega
    rw [e1, e2, e3, e4, rad_gen t (i.natAbs + j.natAbs) 1 3 (by omega)]
    congr 1
    ring
  · have e1 : (i + 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e2 : (i - 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) - 1 := by omega
    have e3 : i.natAbs + (j + 1).natAbs = (i.natAbs + j.natAbs) - 1 := by omega
    have e4 : i.natAbs + (j - 1).natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    rw [e1, e2, e3, e4, rad_gen t (i.natAbs + j.natAbs) 2 2 (by omega)]
    congr 1
    ring
  · have e1 : (i + 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e2 : (i - 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) - 1 := by omega
    have e3 : i.natAbs + (j + 1).natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e4 : i.natAbs + (j - 1).natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    rw [e1, e2, e3, e4, rad_gen t (i.natAbs + j.natAbs) 1 3 (by omega)]
    congr 1
    ring
  · have e1 : (i + 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e2 : (i - 1).natAbs + j.natAbs = (i.natAbs + j.natAbs) - 1 := by omega
    have e3 : i.natAbs + (j + 1).natAbs = (i.natAbs + j.natAbs) + 1 := by omega
    have e4 : i.natAbs + (j - 1).natAbs = (i.natAbs + j.natAbs) - 1 := by omega
    rw [e1, e2, e3, e4, rad_gen t (i.natAbs + j.natAbs) 2 2 (by omega)]
    congr 1
    ring

open OMA.S_oeis_a264797 in
lemma cN (t : ℕ) : ∀ i j, cell 342 t i j = q t i j := by
  induction t with
  | zero =>
    intro i j
    show decide (i = 0 ∧ j = 0) = q 0 i j
    unfold q v
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  | succ k ih => exact step_gen 342 k (q k) (q (k + 1)) ih (tr_q k)

lemma two_pts (a b N : ℕ) : ∑ j ∈ Finset.range N, (if j = a ∨ j = b then 1 else 0) =
    (if a < N then 1 else 0) + (if b < N ∧ b ≠ a then 1 else 0) := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

lemma ends (c N : ℕ) (hc : 0 < c) : ∑ i ∈ Finset.range N, (if i = 0 ∨ i = c then 1 else 2) +
    (if 0 < N then 1 else 0) + (if c < N then 1 else 0) = 2 * N := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    split_ifs at ih ⊢ <;> omega

lemma shell_row (N i : ℕ) (hN : 1 ≤ N) (hi : i ≤ 2 * N) :
    ∑ j ∈ Finset.range (2 * N + 1),
      (if ((i : ℤ) - (N : ℤ)).natAbs + ((j : ℤ) - (N : ℤ)).natAbs = N then 1 else 0) =
      (if i = 0 ∨ i = 2 * N then 1 else 2) := by
  have h := two_pts (((i : ℤ) - (N : ℤ)).natAbs) (2 * N - ((i : ℤ) - (N : ℤ)).natAbs) (2 * N + 1)
  have hc : ∀ j ∈ Finset.range (2 * N + 1),
      (if ((i : ℤ) - (N : ℤ)).natAbs + ((j : ℤ) - (N : ℤ)).natAbs = N then 1 else 0) =
      (if j = ((i : ℤ) - (N : ℤ)).natAbs ∨ j = 2 * N - ((i : ℤ) - (N : ℤ)).natAbs then 1 else 0) := by
    intro j hj
    have := Finset.mem_range.mp hj
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [Finset.sum_congr rfl hc, h]
  split_ifs <;> omega

lemma shell_total (N : ℕ) (hN : 1 ≤ N) :
    ∑ i ∈ Finset.range (2 * N + 1), ∑ j ∈ Finset.range (2 * N + 1),
      (if ((i : ℤ) - (N : ℤ)).natAbs + ((j : ℤ) - (N : ℤ)).natAbs = N then 1 else 0) = 4 * N := by
  rw [Finset.sum_congr rfl (fun i hi => shell_row N i hN
    (by have := Finset.mem_range.mp hi; omega))]
  have h := ends (2 * N) (2 * N + 1) (by omega)
  rw [if_pos (by omega), if_pos (by omega)] at h
  omega

lemma split_ind (g : ℕ → ℕ) (m d : ℕ) : (if d ≤ m + 1 then g d else 0) =
    (if d ≤ m then g d else 0) + g (m + 1) * (if d = m + 1 then 1 else 0) := by
  by_cases h1 : d ≤ m
  · have h2 : d ≠ m + 1 := by omega
    have h3 : d ≤ m + 1 := by omega
    simp [h1, h2, h3]
  · by_cases h2 : d = m + 1
    · subst h2
      simp
    · have h3 : ¬ d ≤ m + 1 := by omega
      simp [h1, h2, h3]

lemma radial_count (g : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n + 1), ∑ j ∈ Finset.range (2 * n + 1),
      (if ((i : ℤ) - (n : ℤ)).natAbs + ((j : ℤ) - (n : ℤ)).natAbs ≤ n then
        g (((i : ℤ) - (n : ℤ)).natAbs + ((j : ℤ) - (n : ℤ)).natAbs) else 0) =
      ∑ k ∈ Finset.range (n + 1), (if k = 0 then 1 else 4 * k) * g k := by
  induction n with
  | zero => simp
  | succ m ih =>
    simp only [split_ind]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hw := win2 (fun x y => if x.natAbs + y.natAbs ≤ m then g (x.natAbs + y.natAbs) else 0) m
      (by
        intro x y hxy
        show (if x.natAbs + y.natAbs ≤ m then g (x.natAbs + y.natAbs) else 0) = 0
        rw [if_neg (by omega)]) 1
    rw [hw, ih, shell_total (m + 1) (by omega), Finset.sum_range_succ (n := m + 1)]
    simp
    ring

/-- the number of ON cells after `t` steps, summed over the shells `|i| + |j| = k` -/
def A (t : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (t + 1), (if k = 0 then 1 else 4 * k) * (if v t k then 1 else 0)

open OMA.S_oeis_a264797 in
lemma on_eq (t : ℕ) : onCount 342 t = A t := by
  unfold onCount A
  simp only [cN t, q]
  rw [← radial_count (fun k => if v t k then 1 else 0) t]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases h : ((i : ℤ) - (t : ℤ)).natAbs + ((j : ℤ) - (t : ℤ)).natAbs ≤ t
  · rw [if_pos h]
  · rw [if_neg h]
    have hv : v t (((i : ℤ) - (t : ℤ)).natAbs + ((j : ℤ) - (t : ℤ)).natAbs) = false := by
      simp only [v, decide_eq_false_iff_not]
      omega
    rw [hv]
    rfl

lemma A_main (t : ℕ) : ∑ k ∈ Finset.range (t + 1),
    (if k = 0 then 1 else 4 * k) * (if v (t + 4) k then 1 else 0) = A t := by
  unfold A
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' := Finset.mem_range.mp hk
  have hv : v (t + 4) k = v t k := by
    unfold v
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  rw [hv]

lemma A_even (t : ℕ) (h : t % 2 = 0) : A (t + 4) = A t + 4 * (t + 4) := by
  have hm := A_main t
  unfold A at hm ⊢
  rw [show t + 4 + 1 = (t + 1) + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, hm]
  have v1 : v (t + 4) (t + 1) = false := by
    unfold v; rw [decide_eq_false_iff_not]; omega
  have v2 : v (t + 4) (t + 1 + 1) = false := by
    unfold v; rw [decide_eq_false_iff_not]; omega
  have v3 : v (t + 4) (t + 1 + 1 + 1) = false := by
    unfold v; rw [decide_eq_false_iff_not]; omega
  have v4 : v (t + 4) (t + 1 + 1 + 1 + 1) = true := by
    unfold v; rw [decide_eq_true_eq]; omega
  rw [v1, v2, v3, v4]
  simp <;> omega

lemma A_odd (t : ℕ) (h : t % 2 = 1) : A (t + 4) = A t + 12 * t + 36 := by
  have hm := A_main t
  unfold A at hm ⊢
  rw [show t + 4 + 1 = (t + 1) + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, hm]
  have v1 : v (t + 4) (t + 1) = false := by
    unfold v; rw [decide_eq_false_iff_not]; omega
  have v2 : v (t + 4) (t + 1 + 1) = true := by
    unfold v; rw [decide_eq_true_eq]; omega
  have v3 : v (t + 4) (t + 1 + 1 + 1) = true := by
    unfold v; rw [decide_eq_true_eq]; omega
  have v4 : v (t + 4) (t + 1 + 1 + 1 + 1) = true := by
    unfold v; rw [decide_eq_true_eq]; omega
  rw [v1, v2, v3, v4]
  simp <;> omega

lemma A_rec (m : ℕ) : A (m + 8) + 2 * A (m + 2) = 2 * A (m + 6) + A m := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · have h1 := A_even m h
    have h2 := A_even (m + 2) (by omega)
    have h3 := A_even (m + 4) (by omega)
    rw [show m + 2 + 4 = m + 6 by ring] at h2
    rw [show m + 4 + 4 = m + 8 by ring] at h3
    omega
  · have h1 := A_odd m h
    have h2 := A_odd (m + 2) (by omega)
    have h3 := A_odd (m + 4) (by omega)
    rw [show m + 2 + 4 = m + 6 by ring] at h2
    rw [show m + 4 + 4 = m + 8 by ring] at h3
    omega

lemma A0 : A 0 = 1 := by decide
lemma A1 : A 1 = 5 := by decide
lemma A2 : A 2 = 8 := by decide
lemma A3 : A 3 = 24 := by decide
lemma A4 : A 4 = 17 := by rw [A_even 0 (by norm_num), A0]
lemma A5 : A 5 = 53 := by rw [A_odd 1 (by norm_num), A1]
lemma A6 : A 6 = 32 := by rw [A_even 2 (by norm_num), A2]
lemma A7 : A 7 = 96 := by rw [A_odd 3 (by norm_num), A3]
lemma A8 : A 8 = 49 := by rw [A_even 4 (by norm_num), A4]

open OMA.S_oeis_a264797 in
lemma e0 : (a 0 : ℚ) = 1 := by
  unfold a; push_cast; rw [on_eq, A0]; norm_num

open OMA.S_oeis_a264797 in
lemma e1 : (a 1 : ℚ) = 5 := by
  unfold a; push_cast; rw [on_eq, A1]; norm_num

open OMA.S_oeis_a264797 in
lemma e2 : (a 2 : ℚ) = 8 := by
  unfold a; push_cast; rw [on_eq, A2]; norm_num

open OMA.S_oeis_a264797 in
lemma e3 : (a 3 : ℚ) = 24 := by
  unfold a; push_cast; rw [on_eq, A3]; norm_num

open OMA.S_oeis_a264797 in
lemma e4 : (a 4 : ℚ) = 17 := by
  unfold a; push_cast; rw [on_eq, A4]; norm_num

open OMA.S_oeis_a264797 in
lemma e5 : (a 5 : ℚ) = 53 := by
  unfold a; push_cast; rw [on_eq, A5]; norm_num

open OMA.S_oeis_a264797 in
lemma e6 : (a 6 : ℚ) = 32 := by
  unfold a; push_cast; rw [on_eq, A6]; norm_num

open OMA.S_oeis_a264797 in
lemma e7 : (a 7 : ℚ) = 96 := by
  unfold a; push_cast; rw [on_eq, A7]; norm_num

open OMA.S_oeis_a264797 in
lemma recQ (m : ℕ) : (a (m + 8) : ℚ) = 2 * a (m + 6) - 2 * a (m + 2) + a m := by
  unfold a
  push_cast
  rw [on_eq, on_eq, on_eq, on_eq]
  have h := A_rec m
  have h2 : ((A (m + 8) : ℕ) : ℚ) + 2 * (A (m + 2) : ℚ) = 2 * (A (m + 6) : ℚ) + (A m : ℚ) := by
    exact_mod_cast h
  linarith

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A264797Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a264797 A264797Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a264797.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [show m + 8 - 2 = m + 6 by omega, show m + 8 - 6 = m + 2 by omega, show m + 8 - 8 = m by omega]
    linarith [recQ m]
  · have hD : ((1 - X) ^ 3 * (1 + X) ^ 3 * (1 + X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-2) * PowerSeries.X ^ 2 + PowerSeries.C 2 * PowerSeries.X ^ 6 + PowerSeries.C (-1) * PowerSeries.X ^ 8 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 5 * X + 6 * X ^ 2 + 14 * X ^ 3 + X ^ 4 + 5 * X ^ 5 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 5 * PowerSeries.X ^ 1 + PowerSeries.C 6 * PowerSeries.X ^ 2 + PowerSeries.C 14 * PowerSeries.X ^ 3 + PowerSeries.C 1 * PowerSeries.X ^ 4 + PowerSeries.C 5 * PowerSeries.X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e1]
    · norm_num [e0, e2]
    · norm_num [e1, e3]
    · norm_num [e2, e4]
    · norm_num [e3, e5]
    · norm_num [e0, e4, e6]
    · norm_num [e1, e5, e7]
    · have hr := recQ (n)
      simp [show n + 8 - 2 = n + 6 by omega, show n + 8 - 6 = n + 2 by omega, show n + 8 - 8 = n by omega]
      linarith
