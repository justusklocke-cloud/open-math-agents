import OMAStatements.S_mo_282089
import Mathlib

namespace MO282089

open Finset Polynomial in
lemma coeff_gen (n k : ℕ) :
    (OMA.S_mo_282089.generating n).coeff k
      = (((range n).powerset).filter fun s => OMA.S_mo_282089.weight s = k).card := by
  unfold OMA.S_mo_282089.generating
  rw [Finset.prod_one_add, Polynomial.finsetSum_coeff, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.prod_pow_eq_pow_sum, Polynomial.coeff_X_pow]
  unfold OMA.S_mo_282089.weight
  by_cases h : ∑ i ∈ s, (i + 1) = k
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

open Finset in
lemma weight_compl (n : ℕ) (s : Finset ℕ) (hs : s ⊆ range n) :
    OMA.S_mo_282089.weight s + OMA.S_mo_282089.weight (range n \ s) = n * (n + 1) / 2 := by
  unfold OMA.S_mo_282089.weight
  rw [add_comm, Finset.sum_sdiff hs]
  have h : ∀ m : ℕ, (∑ i ∈ range m, (i + 1)) * 2 = m * (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  have := h n
  omega

end MO282089

open Finset in
theorem OMA.solution : type_of% @OMA.S_mo_282089.main := by
  intro n
  unfold OMA.S_mo_282089.ways
  by_cases hpar : n * (n + 1) / 2 % 2 = 0
  · rw [if_pos hpar, MO282089.coeff_gen]
    congr 1
    apply Finset.filter_congr
    intro s hs
    have hs' := Finset.mem_powerset.mp hs
    have := MO282089.weight_compl n s hs'
    constructor <;> intro h <;> omega
  · rw [if_neg hpar]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro s hs
    have hs' := Finset.mem_powerset.mp hs
    have := MO282089.weight_compl n s hs'
    omega
