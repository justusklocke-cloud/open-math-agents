import OMAStatements.S_oeis_a003285
import Mathlib

namespace A003285Aux

def U (c : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | k + 2 => c (k + 2) * U c (k + 1) + U c k

def V (c : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => c (k + 2) * V c (k + 1) + V c k

lemma U_rec (c : ℕ → ℤ) (k : ℕ) : U c (k + 2) = c (k + 2) * U c (k + 1) + U c k := by
  rw [U]

lemma V_rec (c : ℕ → ℤ) (k : ℕ) : V c (k + 2) = c (k + 2) * V c (k + 1) + V c k := by
  rw [V]

lemma sol_eq (c : ℕ → ℤ) (x : ℕ → ℤ) (hx : ∀ k, x (k + 2) = c (k + 2) * x (k + 1) + x k) :
    ∀ k, x k = x 0 * U c k + x 1 * V c k ∧ x (k + 1) = x 0 * U c (k + 1) + x 1 * V c (k + 1) := by
  intro k
  induction k with
  | zero => simp [U, V]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [hx k, U_rec, V_rec]
    linear_combination c (k + 2) * ih.2 + ih.1

lemma shift (c : ℕ → ℤ) (m : ℕ) (hc : ∀ k, 1 ≤ k → c (k + m) = c k) (x : ℕ → ℤ)
    (hx : ∀ k, x (k + 2) = c (k + 2) * x (k + 1) + x k) :
    ∀ k, x (k + m) = x m * U c k + x (m + 1) * V c k := by
  have hy : ∀ k, (fun j => x (j + m)) (k + 2) =
      c (k + 2) * (fun j => x (j + m)) (k + 1) + (fun j => x (j + m)) k := by
    intro k
    have h := hx (k + m)
    have e : c (k + m + 2) = c (k + 2) := by
      rw [show k + m + 2 = k + 2 + m by ring]
      exact hc (k + 2) (by omega)
    rw [e] at h
    show x (k + 2 + m) = c (k + 2) * x (k + 1 + m) + x (k + m)
    rw [show k + 2 + m = k + m + 2 by ring, show k + 1 + m = k + m + 1 by ring]
    exact h
  intro k
  have h := (sol_eq c (fun j => x (j + m)) hy k).1
  simp only [Nat.zero_add] at h
  rw [show 1 + m = m + 1 by ring] at h
  exact h

lemma wronskian (c : ℕ → ℤ) : ∀ k, U c (k + 1) * V c k - U c k * V c (k + 1) = -(-1) ^ k := by
  intro k
  induction k with
  | zero => simp [U, V]
  | succ k ih =>
    rw [U_rec, V_rec, pow_succ]
    linear_combination -ih

lemma key (c : ℕ → ℤ) (m : ℕ) (hc : ∀ k, 1 ≤ k → c (k + m) = c k) (x : ℕ → ℤ)
    (hx : ∀ k, x (k + 2) = c (k + 2) * x (k + 1) + x k) :
    ∀ k, x (k + 2 * m) = (U c m + V c (m + 1)) * x (k + m) - (-1) ^ m * x k := by
  intro k
  have h1 := shift c m hc x hx (k + m)
  have h2 := shift c m hc (U c) (U_rec c) k
  have h3 := shift c m hc (V c) (V_rec c) k
  have h4 := shift c m hc x hx k
  have h5 := (sol_eq c x hx k).1
  have h6 := (sol_eq c x hx m).1
  have h7 := (sol_eq c x hx m).2
  have hW := wronskian c m
  rw [show k + 2 * m = k + m + m by ring, h1, h2, h3, h4, h5, h6, h7]
  linear_combination (x 0 * U c k + x 1 * V c k) * hW

end A003285Aux

open OMA.S_oeis_a003285 A003285Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a003285.main := by
  intro d hd
  by_cases hne : {m : ℕ | 0 < m ∧ ∀ k : ℕ, 1 ≤ k →
      cfCoeff (Real.sqrt d) (k + m) = cfCoeff (Real.sqrt d) k}.Nonempty
  · have hmem := Nat.sInf_mem hne
    have hper : ∀ k : ℕ, 1 ≤ k →
        cfCoeff (Real.sqrt d) (k + cfPeriod d) = cfCoeff (Real.sqrt d) k := hmem.2
    refine ⟨U (cfCoeff (Real.sqrt d)) (cfPeriod d) + V (cfCoeff (Real.sqrt d)) (cfPeriod d + 1), ?_⟩
    intro m
    refine ⟨?_, ?_⟩
    · exact key (cfCoeff (Real.sqrt d)) (cfPeriod d) hper (convDen (Real.sqrt d))
        (fun k => by rw [convDen])
    · exact key (cfCoeff (Real.sqrt d)) (cfPeriod d) hper (convNum (Real.sqrt d))
        (fun k => by rw [convNum])
  · have hempty := Set.not_nonempty_iff_eq_empty.mp hne
    have hm0 : cfPeriod d = 0 := by
      unfold cfPeriod
      rw [hempty]
      exact Nat.sInf_empty
    refine ⟨2, ?_⟩
    intro m
    have hm : m = 0 := hm0
    rw [hm]
    refine ⟨fun k => ?_, fun k => ?_⟩
    · simp
      ring
    · simp
      ring
