import OMAStatements.S_oeis_a273849
import Mathlib

namespace A273849Aux

open OMA.S_oeis_a273849 in
lemma step_gen (code t : ℕ) (f g : ℤ → ℤ → Bool)
    (hf : ∀ i j, cell code t i j = f i j)
    (h : ∀ (i j : ℤ) (c n1 n2 n3 n4 : Bool), f i j = c → f (i + 1) j = n1 → f (i - 1) j = n2 →
      f i (j + 1) = n3 → f i (j - 1) = n4 →
      g i j = code.testBit (c.toNat + 2 * (n1.toNat + n2.toNat + n3.toNat + n4.toNat))) :
    ∀ i j, cell code (t + 1) i j = g i j := by
  intro i j
  show code.testBit ((cell code t i j).toNat + 2 * ((cell code t (i + 1) j).toNat +
      (cell code t (i - 1) j).toNat + (cell code t i (j + 1)).toNat +
      (cell code t i (j - 1)).toNat)) = g i j
  rw [hf, hf, hf, hf, hf]
  exact (h i j _ _ _ _ _ rfl rfl rfl rfl rfl).symm

def p0 (i j : ℤ) : Bool := decide (i = 0 ∧ j = 0)
def p1 (i j : ℤ) : Bool := decide (¬(-1 ≤ i + j ∧ i + j ≤ 1 ∧ -1 ≤ i - j ∧ i - j ≤ 1))
def p2 (i j : ℤ) : Bool := decide (¬((i = 1 ∨ i = -1) ∧ (j = 1 ∨ j = -1)))
def p3 (i j : ℤ) : Bool :=
  decide (¬((i = 0 ∧ (j = 1 ∨ j = -1)) ∨ (j = 0 ∧ (i = 1 ∨ i = -1))))
def p4 (i j : ℤ) : Bool := decide (¬((i = 0 ∧ j = 0) ∨ ((i = 1 ∨ i = -1) ∧ (j = 1 ∨ j = -1))))
def p5 (_ _ : ℤ) : Bool := true

open OMA.S_oeis_a273849 in
lemma c0 (i j : ℤ) : cell 969 0 i j = p0 i j := rfl

open OMA.S_oeis_a273849 in
lemma c1 : ∀ i j, cell 969 1 i j = p1 i j := by
  refine step_gen 969 0 p0 p1 c0 ?_
  intro i j c n1 n2 n3 n4 h0 h1 h2 h3 h4
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;>
    simp [p0, p1, Nat.testBit_eq_decide_div_mod_eq] at * <;> omega

open OMA.S_oeis_a273849 in
lemma c2 : ∀ i j, cell 969 2 i j = p2 i j := by
  refine step_gen 969 1 p1 p2 c1 ?_
  intro i j c n1 n2 n3 n4 h0 h1 h2 h3 h4
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;>
    simp [p1, p2, Nat.testBit_eq_decide_div_mod_eq] at * <;> omega

open OMA.S_oeis_a273849 in
lemma c3 : ∀ i j, cell 969 3 i j = p3 i j := by
  refine step_gen 969 2 p2 p3 c2 ?_
  intro i j c n1 n2 n3 n4 h0 h1 h2 h3 h4
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;>
    simp [p2, p3, Nat.testBit_eq_decide_div_mod_eq] at * <;> omega

open OMA.S_oeis_a273849 in
lemma c4 : ∀ i j, cell 969 4 i j = p4 i j := by
  refine step_gen 969 3 p3 p4 c3 ?_
  intro i j c n1 n2 n3 n4 h0 h1 h2 h3 h4
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;>
    simp [p3, p4, Nat.testBit_eq_decide_div_mod_eq] at * <;> omega

open OMA.S_oeis_a273849 in
lemma c5 : ∀ i j, cell 969 5 i j = p5 i j := by
  refine step_gen 969 4 p4 p5 c4 ?_
  intro i j c n1 n2 n3 n4 h0 h1 h2 h3 h4
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;>
    simp [p4, p5, Nat.testBit_eq_decide_div_mod_eq] at * <;> omega

open OMA.S_oeis_a273849 in
lemma cN (n : ℕ) : ∀ i j, cell 969 (n + 5) i j = p5 i j := by
  induction n with
  | zero => exact c5
  | succ k ih =>
    refine step_gen 969 (k + 5) p5 p5 ih ?_
    intro i j c n1 n2 n3 n4 h0 h1 h2 h3 h4
    cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;>
      simp [p5, Nat.testBit_eq_decide_div_mod_eq] at *

open OMA.S_oeis_a273849 in
lemma on0 : onCount 969 0 = 1 := by
  unfold onCount; simp only [c0]; decide

open OMA.S_oeis_a273849 in
lemma on1 : onCount 969 1 = 4 := by
  unfold onCount; simp only [c1]; decide

open OMA.S_oeis_a273849 in
lemma on2 : onCount 969 2 = 21 := by
  unfold onCount; simp only [c2]; decide

open OMA.S_oeis_a273849 in
lemma on3 : onCount 969 3 = 45 := by
  unfold onCount; simp only [c3]; decide

open OMA.S_oeis_a273849 in
lemma on4 : onCount 969 4 = 76 := by
  unfold onCount; simp only [c4]; decide

open OMA.S_oeis_a273849 in
lemma onN (n : ℕ) : onCount 969 (n + 5) = (2 * (n + 5) + 1) ^ 2 := by
  unfold onCount
  simp only [cN, p5]
  simp
  ring

open OMA.S_oeis_a273849 in
lemma a_succ (n : ℕ) : a (n + 1) = a n + (onCount 969 (n + 1) : ℤ) := by
  unfold a
  rw [Finset.sum_range_succ]

open OMA.S_oeis_a273849 in
lemma a0 : a 0 = 1 := by
  unfold a; simp [on0]

open OMA.S_oeis_a273849 in
lemma a1 : a 1 = 5 := by
  rw [a_succ, a0, on1]; norm_num

open OMA.S_oeis_a273849 in
lemma a2 : a 2 = 26 := by
  rw [a_succ, a1, on2]; norm_num

open OMA.S_oeis_a273849 in
lemma a3 : a 3 = 71 := by
  rw [a_succ, a2, on3]; norm_num

open OMA.S_oeis_a273849 in
lemma a4 : a 4 = 147 := by
  rw [a_succ, a3, on4]; norm_num

open OMA.S_oeis_a273849 in
lemma a_cl (n : ℕ) : 3 * a (n + 4) =
    4 * ((n : ℤ) + 4) ^ 3 + 12 * ((n : ℤ) + 4) ^ 2 + 11 * ((n : ℤ) + 4) - 51 := by
  induction n with
  | zero => rw [a4]; norm_num
  | succ k ih =>
    rw [show k + 1 + 4 = (k + 4) + 1 by ring, a_succ, show k + 4 + 1 = k + 5 by ring, onN]
    push_cast
    linarith

open OMA.S_oeis_a273849 in
lemma aQ (n : ℕ) : (a (n + 4) : ℚ) =
    (4 * ((n : ℚ) + 4) ^ 3 + 12 * ((n : ℚ) + 4) ^ 2 + 11 * ((n : ℚ) + 4) - 51) / 3 := by
  have h := a_cl n
  have h2 : (3 : ℚ) * (a (n + 4) : ℚ) =
      4 * ((n : ℚ) + 4) ^ 3 + 12 * ((n : ℚ) + 4) ^ 2 + 11 * ((n : ℚ) + 4) - 51 := by
    exact_mod_cast h
  linarith

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A273849Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a273849 A273849Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a273849.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [aQ]
    push_cast
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
      show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega]
    have f8 := aQ (m + 4)
    have f7 := aQ (m + 3)
    have f6 := aQ (m + 2)
    have f5 := aQ (m + 1)
    have f4 := aQ m
    rw [show m + 4 + 4 = m + 8 by ring] at f8
    rw [show m + 3 + 4 = m + 7 by ring] at f7
    rw [show m + 2 + 4 = m + 6 by ring] at f6
    rw [show m + 1 + 4 = m + 5 by ring] at f5
    rw [f8, f7, f6, f5, f4]
    push_cast
    ring
  · have hD : ((1 : PowerSeries ℚ) - PowerSeries.X) ^ 4 =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-4) * PowerSeries.X ^ 1 +
        PowerSeries.C 6 * PowerSeries.X ^ 2 + PowerSeries.C (-4) * PowerSeries.X ^ 3 +
        PowerSeries.C 1 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + PowerSeries.X + 12 * PowerSeries.X ^ 2 - 7 * PowerSeries.X ^ 3
        + 7 * PowerSeries.X ^ 5 - 11 * PowerSeries.X ^ 6 + 5 * PowerSeries.X ^ 7 :
        PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 1 * PowerSeries.X ^ 1 +
        PowerSeries.C 12 * PowerSeries.X ^ 2 + PowerSeries.C (-7) * PowerSeries.X ^ 3 +
        PowerSeries.C 7 * PowerSeries.X ^ 5 + PowerSeries.C (-11) * PowerSeries.X ^ 6 +
        PowerSeries.C 5 * PowerSeries.X ^ 7 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    have e0 : (a 0 : ℚ) = 1 := by rw [a0]; norm_num
    have e1 : (a 1 : ℚ) = 5 := by rw [a1]; norm_num
    have e2 : (a 2 : ℚ) = 26 := by rw [a2]; norm_num
    have e3 : (a 3 : ℚ) = 71 := by rw [a3]; norm_num
    have e4 : (a 4 : ℚ) = 147 := by rw [a4]; norm_num
    have e5 : (a 5 : ℚ) = 268 := by have := aQ 1; norm_num at this; exact this
    have e6 : (a 6 : ℚ) = 437 := by have := aQ 2; norm_num at this; exact this
    have e7 : (a 7 : ℚ) = 662 := by have := aQ 3; norm_num at this; exact this
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
    · simp [e0]
    · simp [e0, e1]; norm_num
    · simp [e0, e1, e2]; norm_num
    · simp [e0, e1, e2, e3]; norm_num
    · simp [e0, e1, e2, e3, e4]; norm_num
    · simp [e1, e2, e3, e4, e5]; norm_num
    · simp [e2, e3, e4, e5, e6]; norm_num
    · simp [e3, e4, e5, e6, e7]; norm_num
    · have f8 := aQ (n + 4)
      have f7 := aQ (n + 3)
      have f6 := aQ (n + 2)
      have f5 := aQ (n + 1)
      have f4 := aQ n
      rw [show n + 4 + 4 = n + 8 by ring] at f8
      rw [show n + 3 + 4 = n + 7 by ring] at f7
      rw [show n + 2 + 4 = n + 6 by ring] at f6
      rw [show n + 1 + 4 = n + 5 by ring] at f5
      simp [show n + 8 - 1 = n + 7 by omega, show n + 8 - 2 = n + 6 by omega,
        show n + 8 - 3 = n + 5 by omega, show n + 8 - 4 = n + 4 by omega, f8, f7, f6, f5, f4]
      ring
