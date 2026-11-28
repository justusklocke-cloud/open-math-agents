import OMAStatements.S_oeis_a267589
import Mathlib

namespace A267589Aux

open OMA.S_oeis_a267589 in
lemma a3 : a 3 = 10 := by decide

open OMA.S_oeis_a267589 in
lemma a4 : a 4 = 20 := by decide

open OMA.S_oeis_a267589 in
lemma a5 : a 5 = 41 := by decide

end A267589Aux

open OMA.S_oeis_a267589 A267589Aux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267589.main) := by
  intro h
  have h5 := h.1 5 (by norm_num)
  rw [show (5 : ℕ) - 1 = 4 from rfl, show (5 : ℕ) - 2 = 3 from rfl, a5, a4, a3] at h5
  norm_num at h5
