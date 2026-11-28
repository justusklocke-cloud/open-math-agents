import OMAStatements.S_oeis_a273769
import Mathlib

namespace A273769Aux
open OMA.S_oeis_a273769 in
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
def p0 (i j : ℤ) : Bool :=
  decide ((i = 0 ∧ j = 0))
def p1 (i j : ℤ) : Bool :=
  decide (¬(((i = -1 ∨ i = 1) ∧ j = 0) ∨ (i = 0 ∧ (-1 ≤ j ∧ j ≤ 1))))
def p2 (i j : ℤ) : Bool :=
  decide (¬(((i = -1 ∨ i = 1) ∧ (-1 ≤ j ∧ j ≤ 1)) ∨ (i = 0 ∧ (j = -1 ∨ j = 1))))
def p3 (i j : ℤ) : Bool :=
  decide (¬((i = 0 ∧ j = 0)))
def p4 (_ _ : ℤ) : Bool := true

lemma far0 (i j : ℤ) (h : i < -0 ∨ 0 < i ∨ j < -0 ∨ 0 < j) : p0 i j = false := by
  simp only [p0, decide_eq_false_iff_not]
  omega

lemma far1 (i j : ℤ) (h : i < -1 ∨ 1 < i ∨ j < -1 ∨ 1 < j) : p1 i j = true := by
  simp only [p1, decide_eq_true_eq]
  omega

lemma far2 (i j : ℤ) (h : i < -1 ∨ 1 < i ∨ j < -1 ∨ 1 < j) : p2 i j = true := by
  simp only [p2, decide_eq_true_eq]
  omega

lemma far3 (i j : ℤ) (h : i < -0 ∨ 0 < i ∨ j < -0 ∨ 0 < j) : p3 i j = true := by
  simp only [p3, decide_eq_true_eq]
  omega

lemma far4 (i j : ℤ) : p4 i j = true := rfl

def box1 : List ℤ := [-1, 0, 1]

lemma mem_box1 (x : ℤ) (h1 : -1 ≤ x) (h2 : x ≤ 1) : x ∈ box1 := by
  unfold box1
  simp
  omega

lemma trbox_0_1 : ∀ i ∈ box1, ∀ j ∈ box1, p1 i j =
    Nat.testBit 913 ((p0 i j).toNat + 2 * ((p0 (i + 1) j).toNat + (p0 (i - 1) j).toNat + (p0 i (j + 1)).toNat + (p0 i (j - 1)).toNat)) := by
  decide

lemma tr_0_1 (i j : ℤ) : p1 i j =
    Nat.testBit 913 ((p0 i j).toNat + 2 * ((p0 (i + 1) j).toNat + (p0 (i - 1) j).toNat + (p0 i (j + 1)).toNat + (p0 i (j - 1)).toNat)) := by
  by_cases h : (-1 ≤ i ∧ i ≤ 1) ∧ (-1 ≤ j ∧ j ≤ 1)
  · exact trbox_0_1 i (mem_box1 i h.1.1 h.1.2) j (mem_box1 j h.2.1 h.2.2)
  · rw [far1 i j (by omega), far0 i j (by omega), far0 (i + 1) j (by omega), far0 (i - 1) j (by omega),
      far0 i (j + 1) (by omega), far0 i (j - 1) (by omega)]
    decide

def box2 : List ℤ := [-2, -1, 0, 1, 2]

lemma mem_box2 (x : ℤ) (h1 : -2 ≤ x) (h2 : x ≤ 2) : x ∈ box2 := by
  unfold box2
  simp
  omega

lemma trbox_1_2 : ∀ i ∈ box2, ∀ j ∈ box2, p2 i j =
    Nat.testBit 913 ((p1 i j).toNat + 2 * ((p1 (i + 1) j).toNat + (p1 (i - 1) j).toNat + (p1 i (j + 1)).toNat + (p1 i (j - 1)).toNat)) := by
  decide

lemma tr_1_2 (i j : ℤ) : p2 i j =
    Nat.testBit 913 ((p1 i j).toNat + 2 * ((p1 (i + 1) j).toNat + (p1 (i - 1) j).toNat + (p1 i (j + 1)).toNat + (p1 i (j - 1)).toNat)) := by
  by_cases h : (-2 ≤ i ∧ i ≤ 2) ∧ (-2 ≤ j ∧ j ≤ 2)
  · exact trbox_1_2 i (mem_box2 i h.1.1 h.1.2) j (mem_box2 j h.2.1 h.2.2)
  · rw [far2 i j (by omega), far1 i j (by omega), far1 (i + 1) j (by omega), far1 (i - 1) j (by omega),
      far1 i (j + 1) (by omega), far1 i (j - 1) (by omega)]
    decide

lemma trbox_2_3 : ∀ i ∈ box2, ∀ j ∈ box2, p3 i j =
    Nat.testBit 913 ((p2 i j).toNat + 2 * ((p2 (i + 1) j).toNat + (p2 (i - 1) j).toNat + (p2 i (j + 1)).toNat + (p2 i (j - 1)).toNat)) := by
  decide

lemma tr_2_3 (i j : ℤ) : p3 i j =
    Nat.testBit 913 ((p2 i j).toNat + 2 * ((p2 (i + 1) j).toNat + (p2 (i - 1) j).toNat + (p2 i (j + 1)).toNat + (p2 i (j - 1)).toNat)) := by
  by_cases h : (-2 ≤ i ∧ i ≤ 2) ∧ (-2 ≤ j ∧ j ≤ 2)
  · exact trbox_2_3 i (mem_box2 i h.1.1 h.1.2) j (mem_box2 j h.2.1 h.2.2)
  · rw [far3 i j (by omega), far2 i j (by omega), far2 (i + 1) j (by omega), far2 (i - 1) j (by omega),
      far2 i (j + 1) (by omega), far2 i (j - 1) (by omega)]
    decide

lemma trbox_3_4 : ∀ i ∈ box1, ∀ j ∈ box1, p4 i j =
    Nat.testBit 913 ((p3 i j).toNat + 2 * ((p3 (i + 1) j).toNat + (p3 (i - 1) j).toNat + (p3 i (j + 1)).toNat + (p3 i (j - 1)).toNat)) := by
  decide

lemma tr_3_4 (i j : ℤ) : p4 i j =
    Nat.testBit 913 ((p3 i j).toNat + 2 * ((p3 (i + 1) j).toNat + (p3 (i - 1) j).toNat + (p3 i (j + 1)).toNat + (p3 i (j - 1)).toNat)) := by
  by_cases h : (-1 ≤ i ∧ i ≤ 1) ∧ (-1 ≤ j ∧ j ≤ 1)
  · exact trbox_3_4 i (mem_box1 i h.1.1 h.1.2) j (mem_box1 j h.2.1 h.2.2)
  · rw [far4 i j, far3 i j (by omega), far3 (i + 1) j (by omega), far3 (i - 1) j (by omega),
      far3 i (j + 1) (by omega), far3 i (j - 1) (by omega)]
    decide

lemma trbox_4_4 : ∀ i ∈ box1, ∀ j ∈ box1, p4 i j =
    Nat.testBit 913 ((p4 i j).toNat + 2 * ((p4 (i + 1) j).toNat + (p4 (i - 1) j).toNat + (p4 i (j + 1)).toNat + (p4 i (j - 1)).toNat)) := by
  decide

lemma tr_4_4 (i j : ℤ) : p4 i j =
    Nat.testBit 913 ((p4 i j).toNat + 2 * ((p4 (i + 1) j).toNat + (p4 (i - 1) j).toNat + (p4 i (j + 1)).toNat + (p4 i (j - 1)).toNat)) := by
  by_cases h : (-1 ≤ i ∧ i ≤ 1) ∧ (-1 ≤ j ∧ j ≤ 1)
  · exact trbox_4_4 i (mem_box1 i h.1.1 h.1.2) j (mem_box1 j h.2.1 h.2.2)
  · rw [far4 i j, far4 (i + 1) j, far4 (i - 1) j,
      far4 i (j + 1), far4 i (j - 1)]
    decide

open OMA.S_oeis_a273769 in
lemma c0 : ∀ i j, cell 913 0 i j = p0 i j := by
  intro i j
  rfl

open OMA.S_oeis_a273769 in
lemma c1 : ∀ i j, cell 913 1 i j = p1 i j :=
  step_gen 913 0 p0 p1 c0 tr_0_1

open OMA.S_oeis_a273769 in
lemma c2 : ∀ i j, cell 913 2 i j = p2 i j :=
  step_gen 913 1 p1 p2 c1 tr_1_2

open OMA.S_oeis_a273769 in
lemma c3 : ∀ i j, cell 913 3 i j = p3 i j :=
  step_gen 913 2 p2 p3 c2 tr_2_3

open OMA.S_oeis_a273769 in
lemma c4 : ∀ i j, cell 913 4 i j = p4 i j :=
  step_gen 913 3 p3 p4 c3 tr_3_4

open OMA.S_oeis_a273769 in
lemma cN (t : ℕ) (ht : 4 ≤ t) : ∀ i j, cell 913 t i j = p4 i j := by
  induction t, ht using Nat.le_induction with
  | base => exact c4
  | succ k hk ih => exact step_gen 913 k p4 p4 ih tr_4_4

open OMA.S_oeis_a273769 in
lemma on0 : onCount 913 0 = 1 := by
  unfold onCount
  simp only [c0]
  decide

open OMA.S_oeis_a273769 in
lemma on1 : onCount 913 1 = 4 := by
  unfold onCount
  simp only [c1]
  decide

open OMA.S_oeis_a273769 in
lemma on2 : onCount 913 2 = 17 := by
  unfold onCount
  simp only [c2]
  decide

open OMA.S_oeis_a273769 in
lemma on3 : onCount 913 3 = 48 := by
  unfold onCount
  simp only [c3]
  decide

lemma cnt4 (t : ℕ) : ((∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
    (if p4 ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0) : ℕ) : ℤ) = (2 * (t : ℤ) + 1) ^ 2 := by
  simp [p4]
  ring

open OMA.S_oeis_a273769 in
lemma onN (t : ℕ) (ht : 4 ≤ t) : (onCount 913 t : ℤ) = (2 * (t : ℤ) + 1) ^ 2 := by
  unfold onCount
  simp only [cN t ht]
  exact cnt4 t

open OMA.S_oeis_a273769 in
lemma onQ (t : ℕ) (ht : 4 ≤ t) : (onCount 913 t : ℚ) = (2 * (t : ℚ) + 1) ^ 2 := by
  have h := onN t ht
  have h2 : ((onCount 913 t : ℤ) : ℚ) = (2 * (t : ℚ) + 1) ^ 2 := by rw [h]; push_cast; ring
  exact_mod_cast h2

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

open OMA.S_oeis_a273769 in
lemma oq0 : (onCount 913 0 : ℚ) = 1 := by
  rw [on0]; norm_num

open OMA.S_oeis_a273769 in
lemma oq1 : (onCount 913 1 : ℚ) = 4 := by
  rw [on1]; norm_num

open OMA.S_oeis_a273769 in
lemma oq2 : (onCount 913 2 : ℚ) = 17 := by
  rw [on2]; norm_num

open OMA.S_oeis_a273769 in
lemma oq3 : (onCount 913 3 : ℚ) = 48 := by
  rw [on3]; norm_num

open OMA.S_oeis_a273769 in
lemma oq4 : (onCount 913 4 : ℚ) = 81 := by
  rw [onQ 4 (by norm_num)]; norm_num

open OMA.S_oeis_a273769 in
lemma oq5 : (onCount 913 5 : ℚ) = 121 := by
  rw [onQ 5 (by norm_num)]; norm_num

open OMA.S_oeis_a273769 in
lemma oq6 : (onCount 913 6 : ℚ) = 169 := by
  rw [onQ 6 (by norm_num)]; norm_num

open OMA.S_oeis_a273769 in
lemma oq7 : (onCount 913 7 : ℚ) = 225 := by
  rw [onQ 7 (by norm_num)]; norm_num

open OMA.S_oeis_a273769 in
lemma oq8 : (onCount 913 8 : ℚ) = 289 := by
  rw [onQ 8 (by norm_num)]; norm_num

open OMA.S_oeis_a273769 in
lemma e0 : (a 0 : ℚ) = 3 := by
  unfold a; push_cast; rw [oq1, oq0]; norm_num

open OMA.S_oeis_a273769 in
lemma e1 : (a 1 : ℚ) = 13 := by
  unfold a; push_cast; rw [oq2, oq1]; norm_num

open OMA.S_oeis_a273769 in
lemma e2 : (a 2 : ℚ) = 31 := by
  unfold a; push_cast; rw [oq3, oq2]; norm_num

open OMA.S_oeis_a273769 in
lemma e3 : (a 3 : ℚ) = 33 := by
  unfold a; push_cast; rw [oq4, oq3]; norm_num

open OMA.S_oeis_a273769 in
lemma e4 : (a 4 : ℚ) = 40 := by
  unfold a; push_cast; rw [oq5, oq4]; norm_num

open OMA.S_oeis_a273769 in
lemma e5 : (a 5 : ℚ) = 48 := by
  unfold a; push_cast; rw [oq6, oq5]; norm_num

open OMA.S_oeis_a273769 in
lemma e6 : (a 6 : ℚ) = 56 := by
  unfold a; push_cast; rw [oq7, oq6]; norm_num

open OMA.S_oeis_a273769 in
lemma aQ (n : ℕ) (hn : 4 ≤ n) : (a n : ℚ) = ((2 * ((n : ℚ) + 1) + 1) ^ 2) - ((2 * (n : ℚ) + 1) ^ 2) := by
  unfold a; push_cast; rw [onQ (n + 1) (by omega), onQ n (by omega)]; push_cast; ring

end A273769Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a273769 A273769Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a273769.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [aQ n (by omega)]
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega]
    rw [aQ (m + 6) (by omega), aQ (m + 5) (by omega), aQ (m + 4) (by omega)]
    push_cast
    ring
  · have hD : ((1 - X) ^ 2 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-2) * PowerSeries.X ^ 1 + PowerSeries.C 1 * PowerSeries.X ^ 2 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (3 + 7 * X + 8 * X ^ 2 - 16 * X ^ 3 + 5 * X ^ 4 + X ^ 5 : PowerSeries ℚ) =
        PowerSeries.C 3 * PowerSeries.X ^ 0 + PowerSeries.C 7 * PowerSeries.X ^ 1 + PowerSeries.C 8 * PowerSeries.X ^ 2 + PowerSeries.C (-16) * PowerSeries.X ^ 3 + PowerSeries.C 5 * PowerSeries.X ^ 4 + PowerSeries.C 1 * PowerSeries.X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e0, e1]
    · norm_num [e0, e1, e2]
    · norm_num [e1, e2, e3]
    · norm_num [e2, e3, e4]
    · norm_num [e3, e4, e5]
    · have f4 := aQ (n + 4) (by omega)
      have f5 := aQ (n + 5) (by omega)
      have f6 := aQ (n + 6) (by omega)
      simp [show n + 6 - 1 = n + 5 by omega, show n + 6 - 2 = n + 4 by omega, f4, f5, f6]
      ring
