import OMAStatements.S_oeis_a025060
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a025060.main := by
  intro z
  by_cases h : z = -2 ∨ z = 0 ∨ z = -3
  · refine ⟨4, -3, z + 12, by norm_num, by norm_num, ?_, by norm_num, ?_, ?_, by ring⟩
    all_goals omega
  · simp only [not_or] at h
    refine ⟨2, -1, z + 2, by norm_num, by norm_num, ?_, by norm_num, ?_, ?_, by ring⟩
    all_goals omega
