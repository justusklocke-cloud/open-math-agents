import OMAStatements.S_oeis_a266794
import Mathlib

namespace A266794Aux

def p0 (i : ℤ) : Bool :=
  decide (i = 0)

lemma far0 (i : ℤ) (h : i < -0 ∨ 0 < i) : p0 i = false := by
  simp only [p0, decide_eq_false_iff_not]
  omega
def p1 (i : ℤ) : Bool :=
  decide (¬(i = -1))

lemma far1 (i : ℤ) (h : i < -1 ∨ 1 < i) : p1 i = true := by
  simp only [p1, decide_eq_true_eq]
  omega
def p2 (i : ℤ) : Bool :=
  decide ((-1 ≤ i ∧ i ≤ 0))

lemma far2 (i : ℤ) (h : i < -1 ∨ 1 < i) : p2 i = false := by
  simp only [p2, decide_eq_false_iff_not]
  omega
def p3 (i : ℤ) : Bool :=
  decide (¬(i = -2 ∨ i = 0))

lemma far3 (i : ℤ) (h : i < -2 ∨ 2 < i) : p3 i = true := by
  simp only [p3, decide_eq_true_eq]
  omega
def p4 (i : ℤ) : Bool :=
  decide ((-2 ≤ i ∧ i ≤ 1))

lemma far4 (i : ℤ) (h : i < -2 ∨ 2 < i) : p4 i = false := by
  simp only [p4, decide_eq_false_iff_not]
  omega
def p5 (i : ℤ) : Bool :=
  decide (¬(i = -3 ∨ (-1 ≤ i ∧ i ≤ 1)))

lemma far5 (i : ℤ) (h : i < -3 ∨ 3 < i) : p5 i = true := by
  simp only [p5, decide_eq_true_eq]
  omega
def p6 (i : ℤ) : Bool :=
  decide ((-3 ≤ i ∧ i ≤ 0) ∨ i = 2)

lemma far6 (i : ℤ) (h : i < -3 ∨ 3 < i) : p6 i = false := by
  simp only [p6, decide_eq_false_iff_not]
  omega
def p7 (i : ℤ) : Bool :=
  decide (¬(i = -4 ∨ (-2 ≤ i ∧ i ≤ 0)))

lemma far7 (i : ℤ) (h : i < -4 ∨ 4 < i) : p7 i = true := by
  simp only [p7, decide_eq_true_eq]
  omega
def p8 (i : ℤ) : Bool :=
  decide ((-4 ≤ i ∧ i ≤ -1) ∨ i = 1)

lemma far8 (i : ℤ) (h : i < -4 ∨ 4 < i) : p8 i = false := by
  simp only [p8, decide_eq_false_iff_not]
  omega

def box1 : List ℤ := [-1, 0, 1]

lemma mem_box1 (x : ℤ) (h1 : -1 ≤ x) (h2 : x ≤ 1) : x ∈ box1 := by
  unfold box1
  simp
  omega

lemma trbox0 : ∀ i ∈ box1, p1 i = Nat.testBit 61 (4 * (p0 (i - 1)).toNat + 2 * (p0 i).toNat + (p0 (i + 1)).toNat) := by
  decide

lemma tr0 (i : ℤ) : p1 i = Nat.testBit 61 (4 * (p0 (i - 1)).toNat + 2 * (p0 i).toNat + (p0 (i + 1)).toNat) := by
  by_cases h : -1 ≤ i ∧ i ≤ 1
  · exact trbox0 i (mem_box1 i h.1 h.2)
  · rw [far1 i (by omega), far0 (i - 1) (by omega), far0 i (by omega), far0 (i + 1) (by omega)]
    decide

def box2 : List ℤ := [-2, -1, 0, 1, 2]

lemma mem_box2 (x : ℤ) (h1 : -2 ≤ x) (h2 : x ≤ 2) : x ∈ box2 := by
  unfold box2
  simp
  omega

lemma trbox1 : ∀ i ∈ box2, p2 i = Nat.testBit 61 (4 * (p1 (i - 1)).toNat + 2 * (p1 i).toNat + (p1 (i + 1)).toNat) := by
  decide

lemma tr1 (i : ℤ) : p2 i = Nat.testBit 61 (4 * (p1 (i - 1)).toNat + 2 * (p1 i).toNat + (p1 (i + 1)).toNat) := by
  by_cases h : -2 ≤ i ∧ i ≤ 2
  · exact trbox1 i (mem_box2 i h.1 h.2)
  · rw [far2 i (by omega), far1 (i - 1) (by omega), far1 i (by omega), far1 (i + 1) (by omega)]
    decide

lemma trbox2 : ∀ i ∈ box2, p3 i = Nat.testBit 61 (4 * (p2 (i - 1)).toNat + 2 * (p2 i).toNat + (p2 (i + 1)).toNat) := by
  decide

lemma tr2 (i : ℤ) : p3 i = Nat.testBit 61 (4 * (p2 (i - 1)).toNat + 2 * (p2 i).toNat + (p2 (i + 1)).toNat) := by
  by_cases h : -2 ≤ i ∧ i ≤ 2
  · exact trbox2 i (mem_box2 i h.1 h.2)
  · rw [far3 i (by omega), far2 (i - 1) (by omega), far2 i (by omega), far2 (i + 1) (by omega)]
    decide

def box3 : List ℤ := [-3, -2, -1, 0, 1, 2, 3]

lemma mem_box3 (x : ℤ) (h1 : -3 ≤ x) (h2 : x ≤ 3) : x ∈ box3 := by
  unfold box3
  simp
  omega

lemma trbox3 : ∀ i ∈ box3, p4 i = Nat.testBit 61 (4 * (p3 (i - 1)).toNat + 2 * (p3 i).toNat + (p3 (i + 1)).toNat) := by
  decide

lemma tr3 (i : ℤ) : p4 i = Nat.testBit 61 (4 * (p3 (i - 1)).toNat + 2 * (p3 i).toNat + (p3 (i + 1)).toNat) := by
  by_cases h : -3 ≤ i ∧ i ≤ 3
  · exact trbox3 i (mem_box3 i h.1 h.2)
  · rw [far4 i (by omega), far3 (i - 1) (by omega), far3 i (by omega), far3 (i + 1) (by omega)]
    decide

lemma trbox4 : ∀ i ∈ box3, p5 i = Nat.testBit 61 (4 * (p4 (i - 1)).toNat + 2 * (p4 i).toNat + (p4 (i + 1)).toNat) := by
  decide

lemma tr4 (i : ℤ) : p5 i = Nat.testBit 61 (4 * (p4 (i - 1)).toNat + 2 * (p4 i).toNat + (p4 (i + 1)).toNat) := by
  by_cases h : -3 ≤ i ∧ i ≤ 3
  · exact trbox4 i (mem_box3 i h.1 h.2)
  · rw [far5 i (by omega), far4 (i - 1) (by omega), far4 i (by omega), far4 (i + 1) (by omega)]
    decide

def box4 : List ℤ := [-4, -3, -2, -1, 0, 1, 2, 3, 4]

lemma mem_box4 (x : ℤ) (h1 : -4 ≤ x) (h2 : x ≤ 4) : x ∈ box4 := by
  unfold box4
  simp
  omega

lemma trbox5 : ∀ i ∈ box4, p6 i = Nat.testBit 61 (4 * (p5 (i - 1)).toNat + 2 * (p5 i).toNat + (p5 (i + 1)).toNat) := by
  decide

lemma tr5 (i : ℤ) : p6 i = Nat.testBit 61 (4 * (p5 (i - 1)).toNat + 2 * (p5 i).toNat + (p5 (i + 1)).toNat) := by
  by_cases h : -4 ≤ i ∧ i ≤ 4
  · exact trbox5 i (mem_box4 i h.1 h.2)
  · rw [far6 i (by omega), far5 (i - 1) (by omega), far5 i (by omega), far5 (i + 1) (by omega)]
    decide

lemma trbox6 : ∀ i ∈ box4, p7 i = Nat.testBit 61 (4 * (p6 (i - 1)).toNat + 2 * (p6 i).toNat + (p6 (i + 1)).toNat) := by
  decide

lemma tr6 (i : ℤ) : p7 i = Nat.testBit 61 (4 * (p6 (i - 1)).toNat + 2 * (p6 i).toNat + (p6 (i + 1)).toNat) := by
  by_cases h : -4 ≤ i ∧ i ≤ 4
  · exact trbox6 i (mem_box4 i h.1 h.2)
  · rw [far7 i (by omega), far6 (i - 1) (by omega), far6 i (by omega), far6 (i + 1) (by omega)]
    decide

def box5 : List ℤ := [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]

lemma mem_box5 (x : ℤ) (h1 : -5 ≤ x) (h2 : x ≤ 5) : x ∈ box5 := by
  unfold box5
  simp
  omega

lemma trbox7 : ∀ i ∈ box5, p8 i = Nat.testBit 61 (4 * (p7 (i - 1)).toNat + 2 * (p7 i).toNat + (p7 (i + 1)).toNat) := by
  decide

lemma tr7 (i : ℤ) : p8 i = Nat.testBit 61 (4 * (p7 (i - 1)).toNat + 2 * (p7 i).toNat + (p7 (i + 1)).toNat) := by
  by_cases h : -5 ≤ i ∧ i ≤ 5
  · exact trbox7 i (mem_box5 i h.1 h.2)
  · rw [far8 i (by omega), far7 (i - 1) (by omega), far7 i (by omega), far7 (i + 1) (by omega)]
    decide

open OMA.S_oeis_a266794 in
lemma c0 : ∀ i, row 0 i = p0 i := by
  intro i
  rfl

open OMA.S_oeis_a266794 in
lemma c1 : ∀ i, row 1 i = p1 i := by
  intro i
  show rule (row 0 (i - 1)) (row 0 i) (row 0 (i + 1)) = p1 i
  rw [c0, c0, c0]
  exact (tr0 i).symm

open OMA.S_oeis_a266794 in
lemma c2 : ∀ i, row 2 i = p2 i := by
  intro i
  show rule (row 1 (i - 1)) (row 1 i) (row 1 (i + 1)) = p2 i
  rw [c1, c1, c1]
  exact (tr1 i).symm

open OMA.S_oeis_a266794 in
lemma c3 : ∀ i, row 3 i = p3 i := by
  intro i
  show rule (row 2 (i - 1)) (row 2 i) (row 2 (i + 1)) = p3 i
  rw [c2, c2, c2]
  exact (tr2 i).symm

open OMA.S_oeis_a266794 in
lemma c4 : ∀ i, row 4 i = p4 i := by
  intro i
  show rule (row 3 (i - 1)) (row 3 i) (row 3 (i + 1)) = p4 i
  rw [c3, c3, c3]
  exact (tr3 i).symm

open OMA.S_oeis_a266794 in
lemma c5 : ∀ i, row 5 i = p5 i := by
  intro i
  show rule (row 4 (i - 1)) (row 4 i) (row 4 (i + 1)) = p5 i
  rw [c4, c4, c4]
  exact (tr4 i).symm

open OMA.S_oeis_a266794 in
lemma c6 : ∀ i, row 6 i = p6 i := by
  intro i
  show rule (row 5 (i - 1)) (row 5 i) (row 5 (i + 1)) = p6 i
  rw [c5, c5, c5]
  exact (tr5 i).symm

open OMA.S_oeis_a266794 in
lemma c7 : ∀ i, row 7 i = p7 i := by
  intro i
  show rule (row 6 (i - 1)) (row 6 i) (row 6 (i + 1)) = p7 i
  rw [c6, c6, c6]
  exact (tr6 i).symm

open OMA.S_oeis_a266794 in
lemma c8 : ∀ i, row 8 i = p8 i := by
  intro i
  show rule (row 7 (i - 1)) (row 7 i) (row 7 (i + 1)) = p8 i
  rw [c7, c7, c7]
  exact (tr7 i).symm

open OMA.S_oeis_a266794 in
lemma a4 : a 4 = 5 := by
  unfold a
  simp only [c4]
  decide

open OMA.S_oeis_a266794 in
lemma a6 : a 6 = 8 := by
  unfold a
  simp only [c6]
  decide

open OMA.S_oeis_a266794 in
lemma a8 : a 8 = 12 := by
  unfold a
  simp only [c8]
  decide

end A266794Aux

open OMA.S_oeis_a266794 A266794Aux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a266794.main) := by
  intro h
  have h8 := h.2.1 8 (by norm_num)
  norm_num [a4, a6, a8] at h8
