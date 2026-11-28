import OMAStatements.S_oeis_a267881
import Mathlib

namespace A267881Aux

open OMA.S_oeis_a267881 in
lemma a3 : a 3 = 6 := by decide

open OMA.S_oeis_a267881 in
lemma a4 : a 4 = 9 := by decide

open OMA.S_oeis_a267881 in
lemma a5 : a 5 = 11 := by decide

end A267881Aux

open OMA.S_oeis_a267881 A267881Aux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267881.main) := by
  intro h
  have h5 := h.1 5 (by norm_num)
  norm_num [a3, a4, a5] at h5
