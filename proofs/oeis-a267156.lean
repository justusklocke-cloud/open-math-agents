import OMAStatements.S_oeis_a267156
import Mathlib

namespace A267156Aux

def st (b : Bool) (L : List ℤ) : ℤ → Bool := fun x => xor b (decide (x ∈ L))

open OMA.S_oeis_a267156 in
def stp (g : ℤ → Bool) : ℤ → Bool := fun i => rule (g (i - 1)) (g i) (g (i + 1))

def inBox (lo hi : ℤ) (L : List ℤ) : Prop := ∀ p ∈ L, lo ≤ p ∧ p ≤ hi

def rng (lo hi : ℤ) : List ℤ :=
  (List.range (hi - lo + 3).toNat).map (fun k : ℕ => (k : ℤ) + (lo - 1))

lemma mem_rng (lo hi x : ℤ) (h1 : lo - 1 ≤ x) (h2 : x ≤ hi + 1) : x ∈ rng lo hi := by
  unfold rng
  rw [List.mem_map]
  refine ⟨(x - (lo - 1)).toNat, ?_, ?_⟩
  · rw [List.mem_range]
    omega
  · have h : (((x - (lo - 1)).toNat : ℕ) : ℤ) = x - (lo - 1) := Int.toNat_of_nonneg (by omega)
    omega

lemma st_far (b : Bool) (lo hi : ℤ) (L : List ℤ) (hL : inBox lo hi L) (u : ℤ)
    (h : ¬(lo ≤ u ∧ u ≤ hi)) : st b L u = b := by
  unfold st
  have hm : u ∉ L := fun hm => h (hL _ hm)
  simp [hm]

open OMA.S_oeis_a267156 in
lemma step_st (lo hi : ℤ) (b b' : Bool) (L L' : List ℤ)
    (hL : inBox lo hi L) (hL' : inBox lo hi L')
    (hr : rule b b b = b')
    (hbox : ∀ x ∈ rng lo hi, stp (st b L) x = st b' L' x) :
    stp (st b L) = st b' L' := by
  funext x
  by_cases h : lo - 1 ≤ x ∧ x ≤ hi + 1
  · exact hbox x (mem_rng lo hi x h.1 h.2)
  · rw [st_far b' lo hi L' hL' x (by omega)]
    unfold stp
    rw [st_far b lo hi L hL x (by omega), st_far b lo hi L hL (x - 1) (by omega),
      st_far b lo hi L hL (x + 1) (by omega)]
    exact hr

open OMA.S_oeis_a267156 in
lemma row_zero : row 0 = st false [0] := by
  funext i
  simp [row, st]

open OMA.S_oeis_a267156 in
lemma row_succ (t : ℕ) : row (t + 1) = stp (row t) := by
  funext i
  rfl

open OMA.S_oeis_a267156 in
lemma s0 : row 0 = st false [0] := row_zero

open OMA.S_oeis_a267156 in
lemma s1 : row 1 = st true [0, 1] := by
  rw [row_succ, s0]
  exact step_st (0) (1) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267156 in
lemma s2 : row 2 = st false [-1, 1, 2] := by
  rw [row_succ, s1]
  exact step_st (-1) (2) true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267156 in
lemma s3 : row 3 = st true [-1, 3] := by
  rw [row_succ, s2]
  exact step_st (-1) (3) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267156 in
lemma s4 : row 4 = st false [-2, -1, 0, 2, 3, 4] := by
  rw [row_succ, s3]
  exact step_st (-2) (4) true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267156 in
lemma s5 : row 5 = st true [-1, 3, 5] := by
  rw [row_succ, s4]
  exact step_st (-2) (5) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267156 in
lemma s6 : row 6 = st false [-2, -1, 0, 2, 3, 5, 6] := by
  rw [row_succ, s5]
  exact step_st (-2) (6) true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267156 in
lemma s7 : row 7 = st true [-1, 7] := by
  rw [row_succ, s6]
  exact step_st (-2) (7) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267156 in
lemma s8 : row 8 = st false [-2, -1, 0, 6, 7, 8] := by
  rw [row_succ, s7]
  exact step_st (-2) (8) true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267156 in
lemma s9 : row 9 = st true [-1, 1, 7, 9] := by
  rw [row_succ, s8]
  exact step_st (-2) (9) false true _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267156 in
lemma s10 : row 10 = st false [-2, -1, 1, 2, 6, 7, 9, 10] := by
  rw [row_succ, s9]
  exact step_st (-2) (10) true false _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a267156 in
lemma r0 : row 0 0 = true := by
  rw [s0]
  decide

open OMA.S_oeis_a267156 in
lemma r1 : row 1 0 = false := by
  rw [s1]
  decide

open OMA.S_oeis_a267156 in
lemma r2 : row 2 0 = false := by
  rw [s2]
  decide

open OMA.S_oeis_a267156 in
lemma r3 : row 3 0 = true := by
  rw [s3]
  decide

open OMA.S_oeis_a267156 in
lemma r4 : row 4 0 = true := by
  rw [s4]
  decide

open OMA.S_oeis_a267156 in
lemma r5 : row 5 0 = true := by
  rw [s5]
  decide

open OMA.S_oeis_a267156 in
lemma r6 : row 6 0 = true := by
  rw [s6]
  decide

open OMA.S_oeis_a267156 in
lemma r7 : row 7 0 = true := by
  rw [s7]
  decide

open OMA.S_oeis_a267156 in
lemma r8 : row 8 0 = true := by
  rw [s8]
  decide

open OMA.S_oeis_a267156 in
lemma r9 : row 9 0 = true := by
  rw [s9]
  decide

open OMA.S_oeis_a267156 in
lemma r10 : row 10 0 = false := by
  rw [s10]
  decide

open OMA.S_oeis_a267156 in
lemma a7 : a 7 = 10011111 := by
  simp [a, Finset.sum_range_succ, r0, r1, r2, r3, r4, r5, r6, r7]

open OMA.S_oeis_a267156 in
lemma a8 : a 8 = 100111111 := by
  simp [a, Finset.sum_range_succ, r0, r1, r2, r3, r4, r5, r6, r7, r8]

open OMA.S_oeis_a267156 in
lemma a9 : a 9 = 1001111111 := by
  simp [a, Finset.sum_range_succ, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9]

open OMA.S_oeis_a267156 in
lemma a10 : a 10 = 10011111110 := by
  simp [a, Finset.sum_range_succ, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]

end A267156Aux

open OMA.S_oeis_a267156 A267156Aux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a267156.main) := by
  rintro ⟨-, h, -⟩
  have h10 := h 10 (by norm_num)
  rw [show (10 : ℕ) - 1 = 9 from rfl, show (10 : ℕ) - 2 = 8 from rfl, show (10 : ℕ) - 3 = 7 from rfl,
    a10, a9, a8, a7] at h10
  norm_num at h10
