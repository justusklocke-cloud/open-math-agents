import OMAStatements.S_oeis_a267924
import Mathlib

namespace A267924Aux

/-- the closed form of the rows: row 0 is the single cell, and for `t ≥ 1` every cell is ON
except the cell at position `t - 2` -/
def p (t : ℕ) (i : ℤ) : Bool := decide ((t = 0 ∧ i = 0) ∨ (1 ≤ t ∧ i ≠ (t : ℤ) - 2))

lemma tr (t : ℕ) (i : ℤ) (l c r : Bool) (hl : p t (i - 1) = l) (hc : p t i = c)
    (hr : p t (i + 1) = r) :
    p (t + 1) i = Nat.testBit 245 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;>
    simp only [p, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
      Nat.testBit_eq_decide_div_mod_eq] at hl hc hr ⊢ <;>
    norm_num <;> push_cast <;> omega

open OMA.S_oeis_a267924 in
lemma rowP (t : ℕ) : ∀ i, row t i = p t i := by
  induction t with
  | zero =>
    intro i
    show decide (i = 0) = p 0 i
    unfold p
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  | succ k ih =>
    intro i
    show rule (row k (i - 1)) (row k i) (row k (i + 1)) = p (k + 1) i
    rw [ih, ih, ih]
    exact (tr k i _ _ _ rfl rfl rfl).symm

lemma sum_skip (m : ℕ) (hm : 3 ≤ m) :
    ∑ k ∈ Finset.range m, (if k ≠ 2 then 2 ^ k else 0) + 5 = 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Finset.sum_range_succ, if_pos (by omega), pow_succ]
    omega

open OMA.S_oeis_a267924 in
lemma a_cl (n : ℕ) (hn : 1 ≤ n) : a n + 5 = 2 ^ (2 * n + 1) := by
  unfold a
  rw [← sum_skip (2 * n + 1) (by omega)]
  congr 1
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' := Finset.mem_range.mp hk
  rw [rowP]
  have e : p n ((n : ℤ) - (k : ℤ)) = decide (k ≠ 2) := by
    unfold p
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  rw [e]
  simp

open OMA.S_oeis_a267924 in
lemma aZ (m : ℕ) : (a (m + 1) : ℤ) = 8 * 4 ^ m - 5 := by
  have h := a_cl (m + 1) (by omega)
  have h2 : ((a (m + 1) : ℕ) : ℤ) + 5 = 2 ^ (2 * (m + 1) + 1) := by exact_mod_cast h
  have h3 : (2 : ℤ) ^ (2 * (m + 1) + 1) = 8 * 4 ^ m := by
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, pow_add, pow_mul]
    norm_num
    ring
  linarith

open OMA.S_oeis_a267924 in
lemma a0 : a 0 = 1 := by decide

open PowerSeries in
lemma coeff_term (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267924Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267924 A267924Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267924.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    rw [aZ (m + 2), aZ (m + 1), aZ m]
    ring
  · have hD : ((1 - X) * (1 - 4 * X) : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-5) * PowerSeries.X ^ 1 +
        PowerSeries.C 4 * PowerSeries.X ^ 2 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 - 2 * X + 16 * X ^ 2 : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-2) * PowerSeries.X ^ 1 +
        PowerSeries.C 16 * PowerSeries.X ^ 2 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    have e0 : (a 0 : ℤ) = 1 := by rw [a0]; norm_num
    have e1 : (a 1 : ℤ) = 3 := by have := aZ 0; norm_num at this; exact this
    have e2 : (a 2 : ℤ) = 27 := by have := aZ 1; norm_num at this; exact this
    rcases n with _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e0, e1]
    · norm_num [e0, e1, e2]
    · have f3 := aZ (n + 2)
      have f2 := aZ (n + 1)
      have f1 := aZ n
      simp [show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega, f3, f2, f1]
      ring
