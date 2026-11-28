import OMAStatements.S_oeis_a273316
import Mathlib

namespace A273316Aux
open OMA.S_oeis_a273316 in
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

lemma far0 (i j : ℤ) (h : i < -0 ∨ 0 < i ∨ j < -0 ∨ 0 < j) : p0 i j = false := by
  simp only [p0, decide_eq_false_iff_not]
  omega

lemma far1 (i j : ℤ) (h : i < -0 ∨ 0 < i ∨ j < -0 ∨ 0 < j) : p1 i j = true := by
  simp only [p1, decide_eq_true_eq]
  omega

def box1 : List ℤ := [-1, 0, 1]

lemma mem_box1 (x : ℤ) (h1 : -1 ≤ x) (h2 : x ≤ 1) : x ∈ box1 := by
  unfold box1
  simp
  omega

lemma trbox_0_1 : ∀ i ∈ box1, ∀ j ∈ box1, p1 i j =
    Nat.testBit 645 ((p0 i j).toNat + 2 * ((p0 (i + 1) j).toNat + (p0 (i - 1) j).toNat + (p0 i (j + 1)).toNat + (p0 i (j - 1)).toNat)) := by
  decide

lemma tr_0_1 (i j : ℤ) : p1 i j =
    Nat.testBit 645 ((p0 i j).toNat + 2 * ((p0 (i + 1) j).toNat + (p0 (i - 1) j).toNat + (p0 i (j + 1)).toNat + (p0 i (j - 1)).toNat)) := by
  by_cases h : (-1 ≤ i ∧ i ≤ 1) ∧ (-1 ≤ j ∧ j ≤ 1)
  · exact trbox_0_1 i (mem_box1 i h.1.1 h.1.2) j (mem_box1 j h.2.1 h.2.2)
  · rw [far1 i j (by omega), far0 i j (by omega), far0 (i + 1) j (by omega), far0 (i - 1) j (by omega),
      far0 i (j + 1) (by omega), far0 i (j - 1) (by omega)]
    decide

lemma trbox_1_1 : ∀ i ∈ box1, ∀ j ∈ box1, p1 i j =
    Nat.testBit 645 ((p1 i j).toNat + 2 * ((p1 (i + 1) j).toNat + (p1 (i - 1) j).toNat + (p1 i (j + 1)).toNat + (p1 i (j - 1)).toNat)) := by
  decide

lemma tr_1_1 (i j : ℤ) : p1 i j =
    Nat.testBit 645 ((p1 i j).toNat + 2 * ((p1 (i + 1) j).toNat + (p1 (i - 1) j).toNat + (p1 i (j + 1)).toNat + (p1 i (j - 1)).toNat)) := by
  by_cases h : (-1 ≤ i ∧ i ≤ 1) ∧ (-1 ≤ j ∧ j ≤ 1)
  · exact trbox_1_1 i (mem_box1 i h.1.1 h.1.2) j (mem_box1 j h.2.1 h.2.2)
  · rw [far1 i j (by omega), far1 (i + 1) j (by omega), far1 (i - 1) j (by omega),
      far1 i (j + 1) (by omega), far1 i (j - 1) (by omega)]
    decide

open OMA.S_oeis_a273316 in
lemma c0 : ∀ i j, cell 645 0 i j = p0 i j := by
  intro i j
  rfl

open OMA.S_oeis_a273316 in
lemma c1 : ∀ i j, cell 645 1 i j = p1 i j :=
  step_gen 645 0 p0 p1 c0 tr_0_1

open OMA.S_oeis_a273316 in
lemma cN (t : ℕ) (ht : 1 ≤ t) : ∀ i j, cell 645 t i j = p1 i j := by
  induction t, ht using Nat.le_induction with
  | base => exact c1
  | succ k hk ih => exact step_gen 645 k p1 p1 ih tr_1_1

open OMA.S_oeis_a273316 in
lemma on0 : onCount 645 0 = 1 := by
  unfold onCount
  simp only [c0]
  decide

lemma cntbox1 : ∑ i ∈ Finset.range (2 * 0 + 1), ∑ j ∈ Finset.range (2 * 0 + 1),
    (if p1 ((i : ℤ) - ((0 : ℕ) : ℤ)) ((j : ℤ) - ((0 : ℕ) : ℤ)) then 0 else 1) = 1 := by
  decide

lemma cnt1 (t : ℕ) (ht : 0 ≤ t) : ((∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
    (if p1 ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0) : ℕ) : ℤ) =
    (2 * (t : ℤ) + 1) ^ 2 - 1 := by
  have h1 := compl2 p1 t
  obtain ⟨m, rfl⟩ : ∃ m, t = 0 + m := ⟨t - 0, by omega⟩
  have h2 := win2 (fun x y => if p1 x y then 0 else 1) 0
    (by intro x y hxy; simp [p1]; omega) m
  rw [cntbox1] at h2
  rw [h2] at h1
  have h3 := congrArg (fun z : ℕ => (z : ℤ)) h1
  simp only [Nat.cast_add, Nat.cast_mul] at h3
  push_cast at h3 ⊢
  linarith

open OMA.S_oeis_a273316 in
lemma onN (t : ℕ) (ht : 1 ≤ t) : (onCount 645 t : ℤ) = (2 * (t : ℤ) + 1) ^ 2 - 1 := by
  unfold onCount
  simp only [cN t ht]
  exact cnt1 t (by omega)

open OMA.S_oeis_a273316 in
lemma onQ (t : ℕ) (ht : 1 ≤ t) : (onCount 645 t : ℚ) = (2 * (t : ℚ) + 1) ^ 2 - 1 := by
  have h := onN t ht
  have h2 : ((onCount 645 t : ℤ) : ℚ) = (2 * (t : ℚ) + 1) ^ 2 - 1 := by rw [h]; push_cast; ring
  exact_mod_cast h2

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

open OMA.S_oeis_a273316 in
lemma oq0 : (onCount 645 0 : ℚ) = 1 := by
  rw [on0]; norm_num

open OMA.S_oeis_a273316 in
lemma oq1 : (onCount 645 1 : ℚ) = 8 := by
  rw [onQ 1 (by norm_num)]; norm_num

open OMA.S_oeis_a273316 in
lemma oq2 : (onCount 645 2 : ℚ) = 24 := by
  rw [onQ 2 (by norm_num)]; norm_num

open OMA.S_oeis_a273316 in
lemma oq3 : (onCount 645 3 : ℚ) = 48 := by
  rw [onQ 3 (by norm_num)]; norm_num

open OMA.S_oeis_a273316 in
lemma oq4 : (onCount 645 4 : ℚ) = 80 := by
  rw [onQ 4 (by norm_num)]; norm_num

open OMA.S_oeis_a273316 in
lemma oq5 : (onCount 645 5 : ℚ) = 120 := by
  rw [onQ 5 (by norm_num)]; norm_num

open OMA.S_oeis_a273316 in
lemma oq6 : (onCount 645 6 : ℚ) = 168 := by
  rw [onQ 6 (by norm_num)]; norm_num

open OMA.S_oeis_a273316 in
lemma oq7 : (onCount 645 7 : ℚ) = 224 := by
  rw [onQ 7 (by norm_num)]; norm_num

open OMA.S_oeis_a273316 in
lemma aS (n : ℕ) : (a (n + 1) : ℚ) = a n + (onCount 645 (n + 1) : ℚ) := by
  unfold a; rw [Finset.sum_range_succ]; push_cast; ring

open OMA.S_oeis_a273316 in
lemma e0 : (a 0 : ℚ) = 1 := by
  unfold a; rw [Finset.sum_range_one]; push_cast; rw [oq0]

open OMA.S_oeis_a273316 in
lemma e1 : (a 1 : ℚ) = 9 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, aS, e0, oq1]; norm_num

open OMA.S_oeis_a273316 in
lemma e2 : (a 2 : ℚ) = 33 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, aS, e1, oq2]; norm_num

open OMA.S_oeis_a273316 in
lemma e3 : (a 3 : ℚ) = 81 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, aS, e2, oq3]; norm_num

open OMA.S_oeis_a273316 in
lemma e4 : (a 4 : ℚ) = 161 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, aS, e3, oq4]; norm_num

open OMA.S_oeis_a273316 in
lemma e5 : (a 5 : ℚ) = 281 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, aS, e4, oq5]; norm_num

open OMA.S_oeis_a273316 in
lemma aQ (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (4 * (n : ℚ) ^ 3 + 12 * (n : ℚ) ^ 2 + 8 * (n : ℚ) + 3) / 3 := by
  induction n, hn using Nat.le_induction with
  | base => rw [e1]; norm_num
  | succ k hk ih =>
    rw [aS, ih, onQ (k + 1) (by omega)]; push_cast; ring

end A273316Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a273316 A273316Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a273316.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rcases Nat.lt_or_ge n 1 with hlt | hge
    · interval_cases n
      · rw [e0]; norm_num
    · rw [aQ n hge]
      first | done | ring
  · intro n hn
    rcases Nat.lt_or_ge n 5 with hlt | hge
    · interval_cases n
      · norm_num [e0, e1, e2, e3, e4]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
      simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
      rw [aQ (m + 5) (by omega), aQ (m + 4) (by omega), aQ (m + 3) (by omega), aQ (m + 2) (by omega), aQ (m + 1) (by omega)]
      push_cast
      ring
  · have hD : ((1 - X) ^ 4 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-4) * PowerSeries.X ^ 1 + PowerSeries.C 6 * PowerSeries.X ^ 2 + PowerSeries.C (-4) * PowerSeries.X ^ 3 + PowerSeries.C 1 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : ((1 + X) * (1 + 4 * X - X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 5 * PowerSeries.X ^ 1 + PowerSeries.C 3 * PowerSeries.X ^ 2 + PowerSeries.C (-1) * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e0, e1]
    · norm_num [e0, e1, e2]
    · norm_num [e0, e1, e2, e3]
    · norm_num [e0, e1, e2, e3, e4]
    · have f1 := aQ (n + 1) (by omega)
      have f2 := aQ (n + 2) (by omega)
      have f3 := aQ (n + 3) (by omega)
      have f4 := aQ (n + 4) (by omega)
      have f5 := aQ (n + 5) (by omega)
      simp [show n + 5 - 1 = n + 4 by omega, show n + 5 - 2 = n + 3 by omega, show n + 5 - 3 = n + 2 by omega, show n + 5 - 4 = n + 1 by omega, f1, f2, f3, f4, f5]
      ring
