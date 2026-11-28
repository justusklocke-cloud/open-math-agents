import OMAStatements.S_oeis_a273677
import Mathlib

namespace CAOEISA273677Aux

open OMA.S_oeis_a273677 in
lemma cell_succ' (code t : ℕ) (i j : ℤ) : cell code (t + 1) i j =
    code.testBit ((cell code t i j).toNat + 2 * ((cell code t (i + 1) j).toNat +
      (cell code t (i - 1) j).toNat + (cell code t i (j + 1)).toNat + (cell code t i (j - 1)).toNat)) := by
  rw [cell]

def G (t : ℕ) (i j : ℤ) : Prop :=
  ((t = 0 ∧ i = 0 ∧ j = 0) ∨ (t = 1 ∧ ¬ (i + j ≤ 1 ∧ i - j ≤ 1 ∧ j - i ≤ 1 ∧ -i - j ≤ 1)) ∨ (t = 2 ∧ ¬ ((i + j ≤ 2 ∧ i - j ≤ 2 ∧ j - i ≤ 2 ∧ -i - j ≤ 2) ∧ ¬ (i + j ≤ 1 ∧ i - j ≤ 1 ∧ j - i ≤ 1 ∧ -i - j ≤ 1))) ∨ (3 ≤ t ∧ ¬ ((i + j ≤ (t : ℤ) ∧ i - j ≤ (t : ℤ) ∧ j - i ≤ (t : ℤ) ∧ -i - j ≤ (t : ℤ)) ∧ (i + j + (t : ℤ)) % 2 = 0)))

set_option maxHeartbeats 4000000 in
open OMA.S_oeis_a273677 in
lemma cell_iff : ∀ (t : ℕ) (i j : ℤ), cell 833 t i j = true ↔ G t i j := by
  intro t
  induction t with
  | zero =>
    intro i j
    rw [cell]
    simp only [decide_eq_true_eq]
    unfold G
    omega
  | succ t ih =>
    intro i j
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ 3 ≤ t) with ht | ht | ht | ht
    · rcases (by omega : (i + j + (t : ℤ)) % 2 = 0 ∨ (i + j + (t : ℤ)) % 2 = 1) with hc | hc
      · rcases (by omega : 0 < i ∨ i = 0 ∨ i < 0) with hi | hi | hi
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i - j ≤ (t : ℤ) ∨ i - j ≥ (t : ℤ) + 2) with hr | hr
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · omega
          · rcases (by omega : i - j ≤ (t : ℤ) ∨ i - j ≥ (t : ℤ) + 2) with hr | hr
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : -i + j ≤ (t : ℤ) ∨ -i + j ≥ (t : ℤ) + 2) with hr | hr
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i + j ≤ (t : ℤ) ∨ -i + j ≥ (t : ℤ) + 2) with hr | hr
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i - j ≤ (t : ℤ) ∨ -i - j ≥ (t : ℤ) + 2) with hr | hr
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
      · rcases (by omega : 0 < i ∨ i = 0 ∨ i < 0) with hi | hi | hi
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i - j ≤ (t : ℤ) - 1 ∨ i - j = (t : ℤ) + 1 ∨ i - j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · omega
            · omega
          · rcases (by omega : i - j ≤ (t : ℤ) - 1 ∨ i - j = (t : ℤ) + 1 ∨ i - j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : -i + j ≤ (t : ℤ) - 1 ∨ -i + j = (t : ℤ) + 1 ∨ -i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i + j ≤ (t : ℤ) - 1 ∨ -i + j = (t : ℤ) + 1 ∨ -i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i - j ≤ (t : ℤ) - 1 ∨ -i - j = (t : ℤ) + 1 ∨ -i - j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · omega
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
    · rcases (by omega : (i + j + (t : ℤ)) % 2 = 0 ∨ (i + j + (t : ℤ)) % 2 = 1) with hc | hc
      · rcases (by omega : 0 < i ∨ i = 0 ∨ i < 0) with hi | hi | hi
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i - j ≤ (t : ℤ) ∨ i - j ≥ (t : ℤ) + 2) with hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · omega
            · omega
          · rcases (by omega : i - j ≤ (t : ℤ) ∨ i - j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : -i + j ≤ (t : ℤ) ∨ -i + j ≥ (t : ℤ) + 2) with hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i + j ≤ (t : ℤ) ∨ -i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i - j ≤ (t : ℤ) ∨ -i - j ≥ (t : ℤ) + 2) with hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
      · rcases (by omega : 0 < i ∨ i = 0 ∨ i < 0) with hi | hi | hi
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i - j ≤ (t : ℤ) - 1 ∨ i - j = (t : ℤ) + 1 ∨ i - j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · omega
            · omega
          · rcases (by omega : i - j ≤ (t : ℤ) - 1 ∨ i - j = (t : ℤ) + 1 ∨ i - j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : -i + j ≤ (t : ℤ) - 1 ∨ -i + j = (t : ℤ) + 1 ∨ -i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i + j ≤ (t : ℤ) - 1 ∨ -i + j = (t : ℤ) + 1 ∨ -i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i - j ≤ (t : ℤ) - 1 ∨ -i - j = (t : ℤ) + 1 ∨ -i - j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
    · rcases (by omega : (i + j + (t : ℤ)) % 2 = 0 ∨ (i + j + (t : ℤ)) % 2 = 1) with hc | hc
      · rcases (by omega : 0 < i ∨ i = 0 ∨ i < 0) with hi | hi | hi
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i - j ≤ (t : ℤ) ∨ i - j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · omega
          · rcases (by omega : i - j ≤ (t : ℤ) ∨ i - j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : -i + j ≤ (t : ℤ) ∨ -i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i + j ≤ (t : ℤ) ∨ -i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i - j ≤ (t : ℤ) ∨ -i - j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
      · rcases (by omega : 0 < i ∨ i = 0 ∨ i < 0) with hi | hi | hi
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i - j ≤ (t : ℤ) - 1 ∨ i - j = (t : ℤ) + 1 ∨ i - j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · omega
            · omega
          · rcases (by omega : i - j ≤ (t : ℤ) - 1 ∨ i - j = (t : ℤ) + 1 ∨ i - j ≥ (t : ℤ) + 3) with hr | hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : -i + j ≤ (t : ℤ) - 1 ∨ -i + j = (t : ℤ) + 1 ∨ -i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i + j ≤ (t : ℤ) - 1 ∨ -i + j = (t : ℤ) + 1 ∨ -i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i - j ≤ (t : ℤ) - 1 ∨ -i - j = (t : ℤ) + 1 ∨ -i - j ≥ (t : ℤ) + 3) with hr | hr | hr
            · omega
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
    · rcases (by omega : (i + j + (t : ℤ)) % 2 = 0 ∨ (i + j + (t : ℤ)) % 2 = 1) with hc | hc
      · rcases (by omega : 0 < i ∨ i = 0 ∨ i < 0) with hi | hi | hi
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i - j ≤ (t : ℤ) ∨ i - j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) ∨ i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · omega
          · rcases (by omega : i - j ≤ (t : ℤ) ∨ i - j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : -i + j ≤ (t : ℤ) ∨ -i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i + j ≤ (t : ℤ) ∨ -i + j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i - j ≤ (t : ℤ) ∨ -i - j ≥ (t : ℤ) + 2) with hr | hr
            · have c0 : cell 833 t i j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i j).mp h
                unfold G at h'
                omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
      · rcases (by omega : 0 < i ∨ i = 0 ∨ i < 0) with hi | hi | hi
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i - j ≤ (t : ℤ) - 1 ∨ i - j = (t : ℤ) + 1 ∨ i - j ≥ (t : ℤ) + 3) with hr | hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : i + j ≤ (t : ℤ) - 1 ∨ i + j = (t : ℤ) + 1 ∨ i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · omega
            · omega
          · rcases (by omega : i - j ≤ (t : ℤ) - 1 ∨ i - j = (t : ℤ) + 1 ∨ i - j ≥ (t : ℤ) + 3) with hr | hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
        · rcases (by omega : 0 < j ∨ j = 0 ∨ j < 0) with hj | hj | hj
          · rcases (by omega : -i + j ≤ (t : ℤ) - 1 ∨ -i + j = (t : ℤ) + 1 ∨ -i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i + j ≤ (t : ℤ) - 1 ∨ -i + j = (t : ℤ) + 1 ∨ -i + j ≥ (t : ℤ) + 3) with hr | hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩
          · rcases (by omega : -i - j ≤ (t : ℤ) - 1 ∨ -i - j = (t : ℤ) + 1 ∨ -i - j ≥ (t : ℤ) + 3) with hr | hr | hr
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i - 1) j).mp h
                unfold G at h'
                omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j - 1)).mp h
                unfold G at h'
                omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih (i + 1) j).mp h
                unfold G at h'
                omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = false := Bool.eq_false_iff.mpr (fun h => by
                have h' := (ih i (j + 1)).mp h
                unfold G at h'
                omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun h => absurd h (by decide), fun h => by
                unfold G at h
                omega⟩
            · have c0 : cell 833 t i j = true := (ih i j).mpr (by unfold G; omega)
              have c1 : cell 833 t (i + 1) j = true := (ih (i + 1) j).mpr (by unfold G; omega)
              have c2 : cell 833 t (i - 1) j = true := (ih (i - 1) j).mpr (by unfold G; omega)
              have c3 : cell 833 t i (j + 1) = true := (ih i (j + 1)).mpr (by unfold G; omega)
              have c4 : cell 833 t i (j - 1) = true := (ih i (j - 1)).mpr (by unfold G; omega)
              rw [cell_succ', c0, c1, c2, c3, c4]
              exact ⟨fun _ => by unfold G; omega, fun _ => by decide⟩

lemma diamond_card (t : ℕ) (S : Finset (ℕ × ℕ))
    (hS : ∀ p : ℕ × ℕ, p ∈ S ↔ (p.1 < 2 * t + 1 ∧ p.2 < 2 * t + 1 ∧
      (((p.1 : ℤ) - t) + ((p.2 : ℤ) - t) ≤ t ∧ ((p.1 : ℤ) - t) - ((p.2 : ℤ) - t) ≤ t ∧ ((p.2 : ℤ) - t) - ((p.1 : ℤ) - t) ≤ t ∧ -((p.1 : ℤ) - t) - ((p.2 : ℤ) - t) ≤ t ∧ (((p.1 : ℤ) - t) + ((p.2 : ℤ) - t) + t) % 2 = 0))) :
    S.card = (t + 1) ^ 2 := by
  have h : S.card = ((Finset.range (t + 1)) ×ˢ (Finset.range (t + 1))).card := by
    apply Finset.card_bij' (fun p _ => ((p.1 + p.2 - t) / 2, (p.1 + t - p.2) / 2))
      (fun q _ => (q.1 + q.2, q.1 + t - q.2))
    · intro p hp
      have h := (hS p).mp hp
      simp only [Finset.mem_product, Finset.mem_range]
      omega
    · intro q hq
      simp only [Finset.mem_product, Finset.mem_range] at hq
      apply (hS _).mpr
      simp only
      omega
    · intro p hp
      have h := (hS p).mp hp
      ext <;> simp only <;> omega
    · intro q hq
      simp only [Finset.mem_product, Finset.mem_range] at hq
      ext <;> simp only <;> omega
  rw [h]
  simp [sq]

open OMA.S_oeis_a273677 in
lemma onCount_card (code t : ℕ) : onCount code t =
    (((Finset.range (2 * t + 1)) ×ˢ (Finset.range (2 * t + 1))).filter
      (fun p => cell code t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t) = true)).card := by
  unfold onCount
  rw [Finset.card_filter, Finset.sum_product]

open OMA.S_oeis_a273677 in
lemma offCount_card (code t : ℕ) : onCount code t +
    (((Finset.range (2 * t + 1)) ×ˢ (Finset.range (2 * t + 1))).filter
      (fun p => ¬ (cell code t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t) = true))).card = (2 * t + 1) ^ 2 := by
  rw [onCount_card, Finset.card_filter_add_card_filter_not]
  simp [sq]

open OMA.S_oeis_a273677 in
lemma oc_big (t : ℕ) (ht : 3 ≤ t) : (onCount 833 t : ℤ) = (2 * (t : ℤ) + 1) ^ 2 - ((t : ℤ) + 1) ^ 2 := by
  have h1 := offCount_card 833 t
  have h2 : (((Finset.range (2 * t + 1)) ×ˢ (Finset.range (2 * t + 1))).filter
      (fun p => ¬ (cell 833 t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t) = true))).card = (t + 1) ^ 2 := by
    apply diamond_card
    intro p
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range, cell_iff]
    unfold G
    constructor
    · intro h
      refine ⟨h.1.1, h.1.2, ?_⟩
      omega
    · intro h
      refine ⟨⟨h.1, h.2.1⟩, ?_⟩
      omega
  rw [h2] at h1
  have h3 : ((onCount 833 t : ℕ) : ℤ) + ((t : ℤ) + 1) ^ 2 = (2 * (t : ℤ) + 1) ^ 2 := by
    exact_mod_cast h1
  linarith

open OMA.S_oeis_a273677 in
lemma ocE (m : ℕ) : (onCount 833 (4 + 2 * m) : ℤ) = (2 * (4 + 2 * (m : ℤ)) + 1) ^ 2 - ((4 + 2 * (m : ℤ)) + 1) ^ 2 := by
  rw [oc_big (4 + 2 * m) (by omega)]
  push_cast
  ring

open OMA.S_oeis_a273677 in
lemma ocO (m : ℕ) : (onCount 833 (4 + 2 * m + 1) : ℤ) = (2 * (4 + 2 * (m : ℤ) + 1) + 1) ^ 2 - ((4 + 2 * (m : ℤ) + 1) + 1) ^ 2 := by
  rw [oc_big (4 + 2 * m + 1) (by omega)]
  push_cast
  ring

open OMA.S_oeis_a273677 in
lemma oc0 : onCount 833 0 = 1 := by decide

open OMA.S_oeis_a273677 in
lemma oc1 : onCount 833 1 = 4 := by decide

open OMA.S_oeis_a273677 in
lemma oc2 : onCount 833 2 = 17 := by decide

open OMA.S_oeis_a273677 in
lemma oc3 : onCount 833 3 = 33 := by
  have h := oc_big 3 (by norm_num)
  norm_num at h
  exact_mod_cast h

open OMA.S_oeis_a273677 in
lemma oc4 : onCount 833 4 = 56 := by
  have h := oc_big 4 (by norm_num)
  norm_num at h
  exact_mod_cast h

open OMA.S_oeis_a273677 in
lemma oc5 : onCount 833 5 = 85 := by
  have h := oc_big 5 (by norm_num)
  norm_num at h
  exact_mod_cast h


open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

open OMA.S_oeis_a273677 in
lemma oc_eq (n : ℕ) (hn : 4 ≤ n) : (onCount 833 n : ℚ) = ((2 : ℚ) * (n : ℚ) + (3 : ℚ) * (n : ℚ) ^ 2) + (-1 : ℚ) ^ n * ((0 : ℚ)) := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 4 + 2 * m ∨ n = 4 + 2 * m + 1 := ⟨(n - 4) / 2, by omega⟩
  · have hs : (-1 : ℚ) ^ (4 + 2 * m) = 1 := Even.neg_one_pow ⟨2 + m, by ring⟩
    have h := ocE m
    have h' : ((onCount 833 (4 + 2 * m) : ℕ) : ℚ) = (((onCount 833 (4 + 2 * m) : ℕ) : ℤ) : ℚ) := by norm_cast
    rw [h', h, hs]
    push_cast
    ring
  · have hs : (-1 : ℚ) ^ (4 + 2 * m + 1) = -1 := Odd.neg_one_pow ⟨2 + m, by ring⟩
    have h := ocO m
    have h' : ((onCount 833 (4 + 2 * m + 1) : ℕ) : ℚ) = (((onCount 833 (4 + 2 * m + 1) : ℕ) : ℤ) : ℚ) := by norm_cast
    rw [h', h, hs]
    push_cast
    ring

open OMA.S_oeis_a273677 in
lemma a_eq (n : ℕ) (hn : 4 ≤ n) : (a n : ℚ) = ((1 : ℚ) + ((3 : ℚ) / 2) * (n : ℚ) + ((5 : ℚ) / 2) * (n : ℚ) ^ 2 + (1 : ℚ) * (n : ℚ) ^ 3) + (-1 : ℚ) ^ n * ((0 : ℚ)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5]
  | succ k hk ih =>
    have e : (a (k + 1) : ℚ) = (a k : ℚ) + (onCount 833 (k + 1) : ℚ) := by
      unfold a
      rw [Finset.sum_range_succ]
      push_cast
      ring
    rw [e, ih, oc_eq (k + 1) (by omega), pow_succ]
    push_cast
    ring

open OMA.S_oeis_a273677 in
lemma av0 : (a 0 : ℚ) = 1 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5]

open OMA.S_oeis_a273677 in
lemma av1 : (a 1 : ℚ) = 5 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5]

open OMA.S_oeis_a273677 in
lemma av2 : (a 2 : ℚ) = 22 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5]

open OMA.S_oeis_a273677 in
lemma av3 : (a 3 : ℚ) = 55 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5]

open OMA.S_oeis_a273677 in
lemma av4 : (a 4 : ℚ) = 111 := by
  rw [a_eq 4 (by norm_num)]
  norm_num

open OMA.S_oeis_a273677 in
lemma av5 : (a 5 : ℚ) = 196 := by
  rw [a_eq 5 (by norm_num)]
  norm_num

open OMA.S_oeis_a273677 in
lemma av6 : (a 6 : ℚ) = 316 := by
  rw [a_eq 6 (by norm_num)]
  norm_num

open OMA.S_oeis_a273677 in
lemma av7 : (a 7 : ℚ) = 477 := by
  rw [a_eq 7 (by norm_num)]
  norm_num

open OMA.S_oeis_a273677 in
lemma av8 : (a 8 : ℚ) = 685 := by
  rw [a_eq 8 (by norm_num)]
  norm_num

end CAOEISA273677Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a273677 CAOEISA273677Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a273677.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n
      · rw [av2]
        norm_num
      · rw [av3]
        norm_num
    · rw [a_eq n h]
      ring
  · intro n hn
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n
      · norm_num [av2, av3, av4, av5, av6]
      · norm_num [av3, av4, av5, av6, av7]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      rw [show m + 8 - 1 = m + 7 from by omega, show m + 8 - 2 = m + 6 from by omega, show m + 8 - 3 = m + 5 from by omega, show m + 8 - 4 = m + 4 from by omega]
      rw [a_eq (m + 8) (by omega), a_eq (m + 7) (by omega), a_eq (m + 6) (by omega), a_eq (m + 5) (by omega), a_eq (m + 4) (by omega)]
      push_cast
      ring
  · have hD : (((1 - PowerSeries.X) ^ 4) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-4) * PowerSeries.X ^ 1 + PowerSeries.C 6 * PowerSeries.X ^ 2 + PowerSeries.C (-4) * PowerSeries.X ^ 3 + PowerSeries.C 1 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : ((1 + PowerSeries.X + 8 * PowerSeries.X ^ 2 - 7 * PowerSeries.X ^ 3 + 4 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 1 * PowerSeries.X ^ 1 + PowerSeries.C 8 * PowerSeries.X ^ 2 + PowerSeries.C (-7) * PowerSeries.X ^ 3 + PowerSeries.C 4 * PowerSeries.X ^ 4 + PowerSeries.C (-1) * PowerSeries.X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n
      · norm_num [av0]
      · norm_num [av0, av1]
      · norm_num [av0, av1, av2]
      · norm_num [av0, av1, av2, av3]
      · norm_num [av0, av1, av2, av3, av4]
      · norm_num [av1, av2, av3, av4, av5]
      · norm_num [av2, av3, av4, av5, av6]
      · norm_num [av3, av4, av5, av6, av7]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      rw [if_pos (show 0 ≤ m + 8 from by omega), if_pos (show 1 ≤ m + 8 from by omega), if_pos (show 2 ≤ m + 8 from by omega), if_pos (show 3 ≤ m + 8 from by omega), if_pos (show 4 ≤ m + 8 from by omega)]
      rw [if_neg (show ¬ (m + 8 = 0) from by omega), if_neg (show ¬ (m + 8 = 1) from by omega), if_neg (show ¬ (m + 8 = 2) from by omega), if_neg (show ¬ (m + 8 = 3) from by omega), if_neg (show ¬ (m + 8 = 4) from by omega), if_neg (show ¬ (m + 8 = 5) from by omega)]
      rw [show m + 8 - 0 = m + 8 from by omega, show m + 8 - 1 = m + 7 from by omega, show m + 8 - 2 = m + 6 from by omega, show m + 8 - 3 = m + 5 from by omega, show m + 8 - 4 = m + 4 from by omega]
      rw [a_eq (m + 8) (by omega), a_eq (m + 7) (by omega), a_eq (m + 6) (by omega), a_eq (m + 5) (by omega), a_eq (m + 4) (by omega)]
      push_cast
      ring
