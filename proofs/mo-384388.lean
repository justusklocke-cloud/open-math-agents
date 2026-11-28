import OMAStatements.S_mo_384388
import Mathlib

namespace MO384388Aux

open OMA.S_mo_384388 in
lemma wc_zero (α : ℝ) : weightedCatalan α 0 = 1 := by
  rw [weightedCatalan]

open OMA.S_mo_384388 in
lemma wc_succ (α : ℝ) (n : ℕ) : weightedCatalan α (n + 1) =
    ((n + 1 : ℕ) : ℝ) ^ α * ∑ i : Fin (n + 1), weightedCatalan α i * weightedCatalan α (n - i) := by
  rw [weightedCatalan]

open OMA.S_mo_384388 in
lemma wc_nonneg (α : ℝ) : ∀ n : ℕ, 0 ≤ weightedCatalan α n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [wc_zero]
      norm_num
    | succ m =>
      rw [wc_succ]
      apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (ih i i.isLt) (ih (m - i) (Nat.lt_succ_of_le (Nat.sub_le _ _)))

lemma cat_succ_real (m : ℕ) :
    (catalan (m + 1) : ℝ) = ∑ i : Fin (m + 1), (catalan i : ℝ) * (catalan (m - i) : ℝ) := by
  rw [catalan_succ]
  push_cast
  rfl

open OMA.S_mo_384388 in
lemma wc_upper (α : ℝ) (hα : 0 ≤ α) :
    ∀ n : ℕ, weightedCatalan α n ≤ (catalan n : ℝ) * (n.factorial : ℝ) ^ α := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [wc_zero]
      simp
    | succ m =>
      rw [wc_succ]
      have hsum : ∑ i : Fin (m + 1), weightedCatalan α i * weightedCatalan α (m - i) ≤
          ∑ i : Fin (m + 1), ((catalan i : ℝ) * (catalan (m - i) : ℝ)) * (m.factorial : ℝ) ^ α := by
        apply Finset.sum_le_sum
        intro i _
        have h1 := ih i i.isLt
        have h2 := ih (m - i) (Nat.lt_succ_of_le (Nat.sub_le _ _))
        have h3 : (((i : ℕ).factorial : ℝ)) ^ α * (((m - (i : ℕ)).factorial : ℝ)) ^ α ≤
            (m.factorial : ℝ) ^ α := by
          rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
          apply Real.rpow_le_rpow (by positivity) _ hα
          have hd : (i : ℕ).factorial * (m - (i : ℕ)).factorial ≤ m.factorial :=
            Nat.le_of_dvd (Nat.factorial_pos _)
              (Nat.factorial_mul_factorial_dvd_factorial (Nat.le_of_lt_succ i.isLt))
          exact_mod_cast hd
        have hc1 : (0 : ℝ) ≤ (catalan i : ℝ) := Nat.cast_nonneg _
        have hc2 : (0 : ℝ) ≤ (catalan (m - i) : ℝ) := Nat.cast_nonneg _
        have hf1 : (0 : ℝ) ≤ (((i : ℕ).factorial : ℝ)) ^ α :=
          Real.rpow_nonneg (Nat.cast_nonneg _) _
        calc weightedCatalan α i * weightedCatalan α (m - i)
            ≤ ((catalan i : ℝ) * ((i : ℕ).factorial : ℝ) ^ α) *
                ((catalan (m - i) : ℝ) * ((m - (i : ℕ)).factorial : ℝ) ^ α) :=
              mul_le_mul h1 h2 (wc_nonneg α _) (mul_nonneg hc1 hf1)
          _ = ((catalan i : ℝ) * (catalan (m - i) : ℝ)) *
                ((((i : ℕ).factorial : ℝ)) ^ α * (((m - (i : ℕ)).factorial : ℝ)) ^ α) := by ring
          _ ≤ ((catalan i : ℝ) * (catalan (m - i) : ℝ)) * (m.factorial : ℝ) ^ α :=
              mul_le_mul_of_nonneg_left h3 (mul_nonneg hc1 hc2)
      have hf : (((m + 1).factorial : ℕ) : ℝ) ^ α =
          ((m + 1 : ℕ) : ℝ) ^ α * (m.factorial : ℝ) ^ α := by
        rw [Nat.factorial_succ, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      calc ((m + 1 : ℕ) : ℝ) ^ α *
            ∑ i : Fin (m + 1), weightedCatalan α i * weightedCatalan α (m - i)
          ≤ ((m + 1 : ℕ) : ℝ) ^ α *
            ∑ i : Fin (m + 1), ((catalan i : ℝ) * (catalan (m - i) : ℝ)) * (m.factorial : ℝ) ^ α :=
            mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ = (catalan (m + 1) : ℝ) * (((m + 1).factorial : ℕ) : ℝ) ^ α := by
            rw [cat_succ_real, hf, ← Finset.sum_mul]
            ring

lemma cat_le (n : ℕ) : (catalan n : ℝ) ≤ (4 : ℝ) ^ n / (n + 1) := by
  have h1 : ((n : ℝ) + 1) * (catalan n : ℝ) = (n.centralBinom : ℝ) := by
    exact_mod_cast succ_mul_catalan_eq_centralBinom n
  have h2 : (n.centralBinom : ℝ) ≤ (4 : ℝ) ^ n := by
    have h : n.centralBinom ≤ 4 ^ n := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      calc (2 * n).choose n ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow _ _
        _ = 4 ^ n := by
          rw [pow_mul]
          norm_num
    exact_mod_cast h
  rw [le_div_iff₀ (by positivity)]
  linarith

open OMA.S_mo_384388 in
lemma wc_lower (α : ℝ) :
    ∀ n : ℕ, (2 : ℝ) ^ n * ((n + 1).factorial : ℝ) ^ α ≤ weightedCatalan α (n + 1) := by
  intro n
  induction n with
  | zero =>
    rw [wc_succ]
    simp [wc_zero]
  | succ k ih =>
    rw [wc_succ α (k + 1)]
    have hsum : 2 * weightedCatalan α (k + 1) ≤
        ∑ i : Fin (k + 1 + 1), weightedCatalan α i * weightedCatalan α (k + 1 - i) := by
      rw [← Finset.sum_range (fun i => weightedCatalan α i * weightedCatalan α (k + 1 - i)),
        Finset.sum_range_succ, Finset.sum_range_succ']
      have hmid : 0 ≤ ∑ i ∈ Finset.range k,
          weightedCatalan α (i + 1) * weightedCatalan α (k + 1 - (i + 1)) :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (wc_nonneg α _) (wc_nonneg α _))
      have e1 : weightedCatalan α 0 * weightedCatalan α (k + 1 - 0) = weightedCatalan α (k + 1) := by
        rw [wc_zero, Nat.sub_zero, one_mul]
      have e2 : weightedCatalan α (k + 1) * weightedCatalan α (k + 1 - (k + 1)) =
          weightedCatalan α (k + 1) := by
        rw [Nat.sub_self, wc_zero, mul_one]
      rw [e1, e2]
      linarith
    have hf : (((k + 1 + 1).factorial : ℕ) : ℝ) ^ α =
        ((k + 1 + 1 : ℕ) : ℝ) ^ α * ((k + 1).factorial : ℝ) ^ α := by
      rw [Nat.factorial_succ (k + 1), Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    have hp : (0 : ℝ) ≤ ((k + 1 + 1 : ℕ) : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc (2 : ℝ) ^ (k + 1) * (((k + 1 + 1).factorial : ℕ) : ℝ) ^ α
        = ((k + 1 + 1 : ℕ) : ℝ) ^ α * (2 * ((2 : ℝ) ^ k * ((k + 1).factorial : ℝ) ^ α)) := by
          rw [hf]
          ring
      _ ≤ ((k + 1 + 1 : ℕ) : ℝ) ^ α * (2 * weightedCatalan α (k + 1)) :=
          mul_le_mul_of_nonneg_left (by linarith) hp
      _ ≤ ((k + 1 + 1 : ℕ) : ℝ) ^ α *
          ∑ i : Fin (k + 1 + 1), weightedCatalan α i * weightedCatalan α (k + 1 - i) :=
          mul_le_mul_of_nonneg_left hsum hp

open OMA.S_mo_384388 in
lemma wc_alpha_zero : ∀ n : ℕ, weightedCatalan 0 n = (catalan n : ℝ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [wc_zero, catalan_zero]
      norm_num
    | succ m =>
      rw [wc_succ, cat_succ_real, Real.rpow_zero, one_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [ih i i.isLt, ih (m - i) (Nat.lt_succ_of_le (Nat.sub_le _ _))]

end MO384388Aux

open OMA.S_mo_384388 in
theorem OMA.solution : type_of% @OMA.S_mo_384388.main := by
  intro α hα
  refine ⟨fun n => ⟨MO384388Aux.wc_nonneg α n, MO384388Aux.wc_upper α hα n, ?_⟩,
    MO384388Aux.wc_lower α, MO384388Aux.wc_alpha_zero⟩
  exact mul_le_mul_of_nonneg_right (MO384388Aux.cat_le n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
