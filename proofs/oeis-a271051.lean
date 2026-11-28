import OMAStatements.S_oeis_a271051
import Mathlib

namespace A271051Aux
open OMA.S_oeis_a271051 in
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
  decide (¬((i = 0 ∧ j = 0)))
def p2 (i j : ℤ) : Bool :=
  decide (((i = -1 ∨ i = 1) ∧ j = 0) ∨ (i = 0 ∧ (j = -1 ∨ j = 1)))
def p3 (i j : ℤ) : Bool :=
  decide (¬(((i = -1 ∨ i = 1) ∧ j = 0) ∨ (i = 0 ∧ (-1 ≤ j ∧ j ≤ 1))))
def p4 (i j : ℤ) : Bool :=
  decide (((i = -2 ∨ i = 2) ∧ j = 0) ∨ ((i = -1 ∨ i = 1) ∧ (-1 ≤ j ∧ j ≤ 1)) ∨ (i = 0 ∧ (-2 ≤ j ∧ j ≤ 2)))

lemma far0 (i j : ℤ) (h : i < -0 ∨ 0 < i ∨ j < -0 ∨ 0 < j) : p0 i j = false := by
  simp only [p0, decide_eq_false_iff_not]
  omega

lemma far1 (i j : ℤ) (h : i < -0 ∨ 0 < i ∨ j < -0 ∨ 0 < j) : p1 i j = true := by
  simp only [p1, decide_eq_true_eq]
  omega

lemma far2 (i j : ℤ) (h : i < -1 ∨ 1 < i ∨ j < -1 ∨ 1 < j) : p2 i j = false := by
  simp only [p2, decide_eq_false_iff_not]
  omega

lemma far3 (i j : ℤ) (h : i < -1 ∨ 1 < i ∨ j < -1 ∨ 1 < j) : p3 i j = true := by
  simp only [p3, decide_eq_true_eq]
  omega

lemma far4 (i j : ℤ) (h : i < -2 ∨ 2 < i ∨ j < -2 ∨ 2 < j) : p4 i j = false := by
  simp only [p4, decide_eq_false_iff_not]
  omega

def box1 : List ℤ := [-1, 0, 1]

lemma mem_box1 (x : ℤ) (h1 : -1 ≤ x) (h2 : x ≤ 1) : x ∈ box1 := by
  unfold box1
  simp
  omega

lemma trbox_0_1 : ∀ i ∈ box1, ∀ j ∈ box1, p1 i j =
    Nat.testBit 253 ((p0 i j).toNat + 2 * ((p0 (i + 1) j).toNat + (p0 (i - 1) j).toNat + (p0 i (j + 1)).toNat + (p0 i (j - 1)).toNat)) := by
  decide

lemma tr_0_1 (i j : ℤ) : p1 i j =
    Nat.testBit 253 ((p0 i j).toNat + 2 * ((p0 (i + 1) j).toNat + (p0 (i - 1) j).toNat + (p0 i (j + 1)).toNat + (p0 i (j - 1)).toNat)) := by
  by_cases h : (-1 ≤ i ∧ i ≤ 1) ∧ (-1 ≤ j ∧ j ≤ 1)
  · exact trbox_0_1 i (mem_box1 i h.1.1 h.1.2) j (mem_box1 j h.2.1 h.2.2)
  · rw [far1 i j (by omega), far0 i j (by omega), far0 (i + 1) j (by omega), far0 (i - 1) j (by omega),
      far0 i (j + 1) (by omega), far0 i (j - 1) (by omega)]
    decide

lemma trbox_1_2 : ∀ i ∈ box1, ∀ j ∈ box1, p2 i j =
    Nat.testBit 253 ((p1 i j).toNat + 2 * ((p1 (i + 1) j).toNat + (p1 (i - 1) j).toNat + (p1 i (j + 1)).toNat + (p1 i (j - 1)).toNat)) := by
  decide

lemma tr_1_2 (i j : ℤ) : p2 i j =
    Nat.testBit 253 ((p1 i j).toNat + 2 * ((p1 (i + 1) j).toNat + (p1 (i - 1) j).toNat + (p1 i (j + 1)).toNat + (p1 i (j - 1)).toNat)) := by
  by_cases h : (-1 ≤ i ∧ i ≤ 1) ∧ (-1 ≤ j ∧ j ≤ 1)
  · exact trbox_1_2 i (mem_box1 i h.1.1 h.1.2) j (mem_box1 j h.2.1 h.2.2)
  · rw [far2 i j (by omega), far1 i j (by omega), far1 (i + 1) j (by omega), far1 (i - 1) j (by omega),
      far1 i (j + 1) (by omega), far1 i (j - 1) (by omega)]
    decide

def box2 : List ℤ := [-2, -1, 0, 1, 2]

lemma mem_box2 (x : ℤ) (h1 : -2 ≤ x) (h2 : x ≤ 2) : x ∈ box2 := by
  unfold box2
  simp
  omega

lemma trbox_2_3 : ∀ i ∈ box2, ∀ j ∈ box2, p3 i j =
    Nat.testBit 253 ((p2 i j).toNat + 2 * ((p2 (i + 1) j).toNat + (p2 (i - 1) j).toNat + (p2 i (j + 1)).toNat + (p2 i (j - 1)).toNat)) := by
  decide

lemma tr_2_3 (i j : ℤ) : p3 i j =
    Nat.testBit 253 ((p2 i j).toNat + 2 * ((p2 (i + 1) j).toNat + (p2 (i - 1) j).toNat + (p2 i (j + 1)).toNat + (p2 i (j - 1)).toNat)) := by
  by_cases h : (-2 ≤ i ∧ i ≤ 2) ∧ (-2 ≤ j ∧ j ≤ 2)
  · exact trbox_2_3 i (mem_box2 i h.1.1 h.1.2) j (mem_box2 j h.2.1 h.2.2)
  · rw [far3 i j (by omega), far2 i j (by omega), far2 (i + 1) j (by omega), far2 (i - 1) j (by omega),
      far2 i (j + 1) (by omega), far2 i (j - 1) (by omega)]
    decide

lemma trbox_3_4 : ∀ i ∈ box2, ∀ j ∈ box2, p4 i j =
    Nat.testBit 253 ((p3 i j).toNat + 2 * ((p3 (i + 1) j).toNat + (p3 (i - 1) j).toNat + (p3 i (j + 1)).toNat + (p3 i (j - 1)).toNat)) := by
  decide

lemma tr_3_4 (i j : ℤ) : p4 i j =
    Nat.testBit 253 ((p3 i j).toNat + 2 * ((p3 (i + 1) j).toNat + (p3 (i - 1) j).toNat + (p3 i (j + 1)).toNat + (p3 i (j - 1)).toNat)) := by
  by_cases h : (-2 ≤ i ∧ i ≤ 2) ∧ (-2 ≤ j ∧ j ≤ 2)
  · exact trbox_3_4 i (mem_box2 i h.1.1 h.1.2) j (mem_box2 j h.2.1 h.2.2)
  · rw [far4 i j (by omega), far3 i j (by omega), far3 (i + 1) j (by omega), far3 (i - 1) j (by omega),
      far3 i (j + 1) (by omega), far3 i (j - 1) (by omega)]
    decide

def box3 : List ℤ := [-3, -2, -1, 0, 1, 2, 3]

lemma mem_box3 (x : ℤ) (h1 : -3 ≤ x) (h2 : x ≤ 3) : x ∈ box3 := by
  unfold box3
  simp
  omega

lemma trbox_4_3 : ∀ i ∈ box3, ∀ j ∈ box3, p3 i j =
    Nat.testBit 253 ((p4 i j).toNat + 2 * ((p4 (i + 1) j).toNat + (p4 (i - 1) j).toNat + (p4 i (j + 1)).toNat + (p4 i (j - 1)).toNat)) := by
  decide

lemma tr_4_3 (i j : ℤ) : p3 i j =
    Nat.testBit 253 ((p4 i j).toNat + 2 * ((p4 (i + 1) j).toNat + (p4 (i - 1) j).toNat + (p4 i (j + 1)).toNat + (p4 i (j - 1)).toNat)) := by
  by_cases h : (-3 ≤ i ∧ i ≤ 3) ∧ (-3 ≤ j ∧ j ≤ 3)
  · exact trbox_4_3 i (mem_box3 i h.1.1 h.1.2) j (mem_box3 j h.2.1 h.2.2)
  · rw [far3 i j (by omega), far4 i j (by omega), far4 (i + 1) j (by omega), far4 (i - 1) j (by omega),
      far4 i (j + 1) (by omega), far4 i (j - 1) (by omega)]
    decide

open OMA.S_oeis_a271051 in
lemma c0 : ∀ i j, cell 253 0 i j = p0 i j := by
  intro i j
  rfl

open OMA.S_oeis_a271051 in
lemma c1 : ∀ i j, cell 253 1 i j = p1 i j :=
  step_gen 253 0 p0 p1 c0 tr_0_1

open OMA.S_oeis_a271051 in
lemma c2 : ∀ i j, cell 253 2 i j = p2 i j :=
  step_gen 253 1 p1 p2 c1 tr_1_2

open OMA.S_oeis_a271051 in
lemma c3 : ∀ i j, cell 253 3 i j = p3 i j :=
  step_gen 253 2 p2 p3 c2 tr_2_3

open OMA.S_oeis_a271051 in
lemma c4 : ∀ i j, cell 253 4 i j = p4 i j :=
  step_gen 253 3 p3 p4 c3 tr_3_4

open OMA.S_oeis_a271051 in
lemma cPer (n : ℕ) : (∀ i j, cell 253 (2 * n + 3) i j = p3 i j) ∧
    (∀ i j, cell 253 (2 * n + 3 + 1) i j = p4 i j) := by
  induction n with
  | zero => exact ⟨c3, c4⟩
  | succ k ih =>
    have h1 : ∀ i j, cell 253 (2 * (k + 1) + 3) i j = p3 i j :=
      step_gen 253 (2 * k + 3 + 1) p4 p3 ih.2 tr_4_3
    exact ⟨h1, step_gen 253 (2 * (k + 1) + 3) p3 p4 h1 tr_3_4⟩

open OMA.S_oeis_a271051 in
lemma cA (t : ℕ) (ht : 3 ≤ t) (hp : t % 2 = 1) : ∀ i j, cell 253 t i j = p3 i j := by
  obtain ⟨n, rfl⟩ : ∃ n, t = 2 * n + 3 := ⟨(t - 3) / 2, by omega⟩
  exact (cPer n).1

open OMA.S_oeis_a271051 in
lemma cB (t : ℕ) (ht : 3 ≤ t) (hp : t % 2 = 0) : ∀ i j, cell 253 t i j = p4 i j := by
  obtain ⟨n, rfl⟩ : ∃ n, t = 2 * n + 3 + 1 := ⟨(t - 3 - 1) / 2, by omega⟩
  exact (cPer n).2

open OMA.S_oeis_a271051 in
lemma on0 : onCount 253 0 = 1 := by
  unfold onCount
  simp only [c0]
  decide

open OMA.S_oeis_a271051 in
lemma on1 : onCount 253 1 = 8 := by
  unfold onCount
  simp only [c1]
  decide

open OMA.S_oeis_a271051 in
lemma on2 : onCount 253 2 = 4 := by
  unfold onCount
  simp only [c2]
  decide

lemma cntbox3 : ∑ i ∈ Finset.range (2 * 1 + 1), ∑ j ∈ Finset.range (2 * 1 + 1),
    (if p3 ((i : ℤ) - ((1 : ℕ) : ℤ)) ((j : ℤ) - ((1 : ℕ) : ℤ)) then 0 else 1) = 5 := by
  decide

lemma cnt3 (t : ℕ) (ht : 1 ≤ t) : ((∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
    (if p3 ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0) : ℕ) : ℤ) =
    (2 * (t : ℤ) + 1) ^ 2 - 5 := by
  have h1 := compl2 p3 t
  obtain ⟨m, rfl⟩ : ∃ m, t = 1 + m := ⟨t - 1, by omega⟩
  have h2 := win2 (fun x y => if p3 x y then 0 else 1) 1
    (by intro x y hxy; simp [p3]; omega) m
  rw [cntbox3] at h2
  rw [h2] at h1
  have h3 := congrArg (fun z : ℕ => (z : ℤ)) h1
  simp only [Nat.cast_add, Nat.cast_mul] at h3
  push_cast at h3 ⊢
  linarith

lemma cntbox4 : ∑ i ∈ Finset.range (2 * 2 + 1), ∑ j ∈ Finset.range (2 * 2 + 1),
    (if p4 ((i : ℤ) - ((2 : ℕ) : ℤ)) ((j : ℤ) - ((2 : ℕ) : ℤ)) then 1 else 0) = 13 := by
  decide

lemma cnt4 (t : ℕ) (ht : 2 ≤ t) : ((∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
    (if p4 ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0) : ℕ) : ℤ) = 13 := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 2 + m := ⟨t - 2, by omega⟩
  have h2 := win2 (fun x y => if p4 x y then 1 else 0) 2
    (by intro x y hxy; simp [p4]; omega) m
  rw [h2, cntbox4]
  norm_num

open OMA.S_oeis_a271051 in
lemma onA (t : ℕ) (ht : 3 ≤ t) (hp : t % 2 = 1) : (onCount 253 t : ℤ) = (2 * (t : ℤ) + 1) ^ 2 - 5 := by
  unfold onCount
  simp only [cA t ht hp]
  exact cnt3 t (by omega)

open OMA.S_oeis_a271051 in
lemma onB (t : ℕ) (ht : 3 ≤ t) (hp : t % 2 = 0) : (onCount 253 t : ℤ) = 13 := by
  unfold onCount
  simp only [cB t ht hp]
  exact cnt4 t (by omega)

open OMA.S_oeis_a271051 in
lemma onQ (t : ℕ) (ht : 3 ≤ t) : (onCount 253 t : ℚ) = (1 + (-1 : ℚ) ^ t) / 2 * (13) + (1 - (-1 : ℚ) ^ t) / 2 * ((2 * (t : ℚ) + 1) ^ 2 - 5) := by
  rcases Nat.even_or_odd t with h | h
  · have h1 := onB t ht (Nat.even_iff.mp h)
    have h2 : ((onCount 253 t : ℤ) : ℚ) = 13 := by rw [h1]; push_cast; ring
    rw [h.neg_one_pow]
    have h3 : (onCount 253 t : ℚ) = 13 := by exact_mod_cast h2
    rw [h3]; ring
  · have h1 := onA t ht (Nat.odd_iff.mp h)
    have h2 : ((onCount 253 t : ℤ) : ℚ) = (2 * (t : ℚ) + 1) ^ 2 - 5 := by rw [h1]; push_cast; ring
    rw [h.neg_one_pow]
    have h3 : (onCount 253 t : ℚ) = (2 * (t : ℚ) + 1) ^ 2 - 5 := by exact_mod_cast h2
    rw [h3]; ring

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

open OMA.S_oeis_a271051 in
lemma oq0 : (onCount 253 0 : ℚ) = 1 := by
  rw [on0]; norm_num

open OMA.S_oeis_a271051 in
lemma oq1 : (onCount 253 1 : ℚ) = 8 := by
  rw [on1]; norm_num

open OMA.S_oeis_a271051 in
lemma oq2 : (onCount 253 2 : ℚ) = 4 := by
  rw [on2]; norm_num

open OMA.S_oeis_a271051 in
lemma oq3 : (onCount 253 3 : ℚ) = 44 := by
  rw [onQ 3 (by norm_num)]; norm_num

open OMA.S_oeis_a271051 in
lemma oq4 : (onCount 253 4 : ℚ) = 13 := by
  rw [onQ 4 (by norm_num)]; norm_num

open OMA.S_oeis_a271051 in
lemma oq5 : (onCount 253 5 : ℚ) = 116 := by
  rw [onQ 5 (by norm_num)]; norm_num

open OMA.S_oeis_a271051 in
lemma oq6 : (onCount 253 6 : ℚ) = 13 := by
  rw [onQ 6 (by norm_num)]; norm_num

open OMA.S_oeis_a271051 in
lemma oq7 : (onCount 253 7 : ℚ) = 220 := by
  rw [onQ 7 (by norm_num)]; norm_num

open OMA.S_oeis_a271051 in
lemma oq8 : (onCount 253 8 : ℚ) = 13 := by
  rw [onQ 8 (by norm_num)]; norm_num

open OMA.S_oeis_a271051 in
lemma oq9 : (onCount 253 9 : ℚ) = 356 := by
  rw [onQ 9 (by norm_num)]; norm_num

open OMA.S_oeis_a271051 in
lemma oq10 : (onCount 253 10 : ℚ) = 13 := by
  rw [onQ 10 (by norm_num)]; norm_num

open OMA.S_oeis_a271051 in
lemma oq11 : (onCount 253 11 : ℚ) = 524 := by
  rw [onQ 11 (by norm_num)]; norm_num

open OMA.S_oeis_a271051 in
lemma e0 : (a 0 : ℚ) = 1 := by
  unfold a; push_cast; rw [oq0]

open OMA.S_oeis_a271051 in
lemma e1 : (a 1 : ℚ) = 8 := by
  unfold a; push_cast; rw [oq1]

open OMA.S_oeis_a271051 in
lemma e2 : (a 2 : ℚ) = 4 := by
  unfold a; push_cast; rw [oq2]

open OMA.S_oeis_a271051 in
lemma e3 : (a 3 : ℚ) = 44 := by
  unfold a; push_cast; rw [oq3]

open OMA.S_oeis_a271051 in
lemma e4 : (a 4 : ℚ) = 13 := by
  unfold a; push_cast; rw [oq4]

open OMA.S_oeis_a271051 in
lemma e5 : (a 5 : ℚ) = 116 := by
  unfold a; push_cast; rw [oq5]

open OMA.S_oeis_a271051 in
lemma e6 : (a 6 : ℚ) = 13 := by
  unfold a; push_cast; rw [oq6]

open OMA.S_oeis_a271051 in
lemma e7 : (a 7 : ℚ) = 220 := by
  unfold a; push_cast; rw [oq7]

open OMA.S_oeis_a271051 in
lemma e8 : (a 8 : ℚ) = 13 := by
  unfold a; push_cast; rw [oq8]

open OMA.S_oeis_a271051 in
lemma e9 : (a 9 : ℚ) = 356 := by
  unfold a; push_cast; rw [oq9]

open OMA.S_oeis_a271051 in
lemma aQ (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = (1 + (-1 : ℚ) ^ n) / 2 * (13) + (1 - (-1 : ℚ) ^ n) / 2 * ((2 * (n : ℚ) + 1) ^ 2 - 5) := by
  unfold a; push_cast; rw [onQ n (by omega)]

end A271051Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a271051 A271051Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a271051.main := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hD : ((1 - X) ^ 3 * (1 + X) ^ 3 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-3) * PowerSeries.X ^ 2 + PowerSeries.C 3 * PowerSeries.X ^ 4 + PowerSeries.C (-1) * PowerSeries.X ^ 6 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 8 * X + X ^ 2 + 20 * X ^ 3 + 4 * X ^ 4 + 8 * X ^ 5 - 15 * X ^ 6 - 4 * X ^ 7 + 9 * X ^ 8 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 8 * PowerSeries.X ^ 1 + PowerSeries.C 1 * PowerSeries.X ^ 2 + PowerSeries.C 20 * PowerSeries.X ^ 3 + PowerSeries.C 4 * PowerSeries.X ^ 4 + PowerSeries.C 8 * PowerSeries.X ^ 5 + PowerSeries.C (-15) * PowerSeries.X ^ 6 + PowerSeries.C (-4) * PowerSeries.X ^ 7 + PowerSeries.C 9 * PowerSeries.X ^ 8 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e1]
    · norm_num [e0, e2]
    · norm_num [e1, e3]
    · norm_num [e0, e2, e4]
    · norm_num [e1, e3, e5]
    · norm_num [e0, e2, e4, e6]
    · norm_num [e1, e3, e5, e7]
    · norm_num [e2, e4, e6, e8]
    · have f3 := aQ (n + 3) (by omega)
      have f5 := aQ (n + 5) (by omega)
      have f7 := aQ (n + 7) (by omega)
      have f9 := aQ (n + 9) (by omega)
      simp [show n + 9 - 2 = n + 7 by omega, show n + 9 - 4 = n + 5 by omega, show n + 9 - 6 = n + 3 by omega, f3, f5, f7, f9]
      ring
  · intro n hn hpar
    rw [aQ n (by omega)]
    rw [hpar.neg_one_pow]
    ring
  · intro n hn hpar
    rw [aQ n (by omega)]
    rw [hpar.neg_one_pow]
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    simp only [show m + 9 - 2 = m + 7 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 6 = m + 3 by omega]
    rw [aQ (m + 9) (by omega), aQ (m + 7) (by omega), aQ (m + 5) (by omega), aQ (m + 3) (by omega)]
    push_cast
    ring
