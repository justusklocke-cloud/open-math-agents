import OMAStatements.S_oeis_a266660
import Mathlib

namespace A266660Aux

/-- the closed form of the rows: for even `t ≥ 2` only the cells `t - 1` and `t` are ON, for
odd `t ≥ 3` only these two cells are OFF -/
def p (t : ℕ) (i : ℤ) : Bool :=
  decide ((t = 0 ∧ i = 0) ∨ (t = 1 ∧ i ≠ 1) ∨ (2 ≤ t ∧
    ((t % 2 = 0 ∧ (i = (t : ℤ) - 1 ∨ i = t)) ∨ (t % 2 = 1 ∧ i ≠ (t : ℤ) - 1 ∧ i ≠ t))))

lemma tr (t : ℕ) (i : ℤ) (l c r : Bool) (hl : p t (i - 1) = l) (hc : p t i = c)
    (hr : p t (i + 1) = r) :
    p (t + 1) i = Nat.testBit 47 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;>
    simp only [p, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
      Nat.testBit_eq_decide_div_mod_eq] at hl hc hr ⊢ <;>
    norm_num <;> push_cast <;> omega

open OMA.S_oeis_a266660 in
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

lemma S_even (m : ℕ) (hm : 2 ≤ m) :
    ∑ k ∈ Finset.range m, (if k ≤ 1 then 10 ^ k else 0) = 11 := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Finset.sum_range_succ, if_neg (by omega), ih]

lemma S_odd (m : ℕ) (hm : 2 ≤ m) :
    9 * ∑ k ∈ Finset.range m, (if 2 ≤ k then 10 ^ k else 0) + 100 = 10 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Finset.sum_range_succ, if_pos (by omega), pow_succ]
    omega

open OMA.S_oeis_a266660 in
lemma aE (n : ℕ) (hn : 2 ≤ n) (he : n % 2 = 0) : a n = 11 := by
  unfold a
  rw [← S_even (2 * n + 1) (by omega)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' := Finset.mem_range.mp hk
  rw [rowP]
  have e : p n ((n : ℤ) - (k : ℤ)) = decide (k ≤ 1) := by
    unfold p
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  rw [e]
  simp

open OMA.S_oeis_a266660 in
lemma aO (n : ℕ) (hn : 2 ≤ n) (ho : n % 2 = 1) : 9 * a n + 100 = 10 ^ (2 * n + 1) := by
  unfold a
  rw [← S_odd (2 * n + 1) (by omega)]
  congr 2
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' := Finset.mem_range.mp hk
  rw [rowP]
  have e : p n ((n : ℤ) - (k : ℤ)) = decide (2 ≤ k) := by
    unfold p
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  rw [e]
  simp

open OMA.S_oeis_a266660 in
lemma a0 : a 0 = 1 := by decide

open OMA.S_oeis_a266660 in
lemma a1 : a 1 = 110 := by decide

open OMA.S_oeis_a266660 in
lemma recN (m : ℕ) : a (m + 6) + 10000 * a (m + 2) = 10001 * a (m + 4) := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · rw [aE (m + 6) (by omega) (by omega), aE (m + 4) (by omega) (by omega),
      aE (m + 2) (by omega) (by omega)]
  · have h6 := aO (m + 6) (by omega) (by omega)
    have h4 := aO (m + 4) (by omega) (by omega)
    have h2 := aO (m + 2) (by omega) (by omega)
    have p6 : 10 ^ (2 * (m + 6) + 1) = 100000000 * 10 ^ (2 * (m + 2) + 1) := by
      rw [show 2 * (m + 6) + 1 = 8 + (2 * (m + 2) + 1) by ring, pow_add]
      norm_num
    have p4 : 10 ^ (2 * (m + 4) + 1) = 10000 * 10 ^ (2 * (m + 2) + 1) := by
      rw [show 2 * (m + 4) + 1 = 4 + (2 * (m + 2) + 1) by ring, pow_add]
      norm_num
    rw [p6] at h6
    rw [p4] at h4
    omega

open OMA.S_oeis_a266660 in
lemma recZ (m : ℕ) : (a (m + 6) : ℤ) = 10001 * a (m + 4) - 10000 * a (m + 2) := by
  have h := recN m
  have h2 : ((a (m + 6) : ℕ) : ℤ) + 10000 * (a (m + 2) : ℤ) = 10001 * (a (m + 4) : ℤ) := by
    exact_mod_cast h
  linarith

open OMA.S_oeis_a266660 in
lemma aOQ (n : ℕ) (hn : 2 ≤ n) (ho : n % 2 = 1) :
    (9 : ℚ) * (a n : ℚ) + 100 = 10 ^ (2 * n + 1) := by
  have h := aO n hn ho
  exact_mod_cast h

open PowerSeries in
lemma coeff_term (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A266660Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a266660 A266660Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a266660.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rcases Nat.even_or_odd n with he | ho
    · rw [aE n (by omega) (Nat.even_iff.mp he), he.neg_one_pow]
      norm_num
    · have h := aOQ n (by omega) (Nat.odd_iff.mp ho)
      rw [ho.neg_one_pow, eq_div_iff (by norm_num)]
      linarith
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega]
    exact recZ m
  · have hD : ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-10001) * PowerSeries.X ^ 2 +
        PowerSeries.C 10000 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 110 * X - 9990 * X ^ 2 + 10990 * X ^ 3 - 100000 * X ^ 4 + 100000 * X ^ 5 :
        PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 110 * PowerSeries.X ^ 1 +
        PowerSeries.C (-9990) * PowerSeries.X ^ 2 + PowerSeries.C 10990 * PowerSeries.X ^ 3 +
        PowerSeries.C (-100000) * PowerSeries.X ^ 4 + PowerSeries.C 100000 * PowerSeries.X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    have e0 : (a 0 : ℤ) = 1 := by rw [a0]; norm_num
    have e1 : (a 1 : ℤ) = 110 := by rw [a1]; norm_num
    have e2 : (a 2 : ℤ) = 11 := by rw [aE 2 (by norm_num) (by norm_num)]; norm_num
    have e3 : (a 3 : ℤ) = 1111100 := by
      have h := aO 3 (by norm_num) (by norm_num)
      norm_num at h
      omega
    have e4 : (a 4 : ℤ) = 11 := by rw [aE 4 (by norm_num) (by norm_num)]; norm_num
    have e5 : (a 5 : ℤ) = 11111111100 := by
      have h := aO 5 (by norm_num) (by norm_num)
      norm_num at h
      omega
    rcases n with _ | _ | _ | _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e1]
    · norm_num [e0, e2]
    · norm_num [e1, e3]
    · norm_num [e0, e2, e4]
    · norm_num [e1, e3, e5]
    · have hr := recZ n
      simp [show n + 6 - 2 = n + 4 by omega, show n + 6 - 4 = n + 2 by omega]
      linarith
  · intro n hn ho
    have h := aOQ n (by omega) (Nat.odd_iff.mp ho)
    have hp : (10 : ℚ) ^ (2 * n + 1) = 10 * 100 ^ n := by
      rw [pow_succ, pow_mul]
      norm_num
      ring
    rw [eq_div_iff (by norm_num)]
    linarith
  · intro n hn he
    exact aE n (by omega) (Nat.even_iff.mp he)
