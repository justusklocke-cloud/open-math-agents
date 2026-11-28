import OMAStatements.S_oeis_a068779
import Mathlib

namespace A068779Proof
open OMA.S_oeis_a068779

lemma quot_lt_ten (a : ℕ) (hpos : 0 < a) (hmod : a % 10 ≠ 0) : a / digitReversal a < 10 := by
  have hd : Nat.digits 10 a = (a % 10) :: Nat.digits 10 (a / 10) :=
    Nat.digits_def' (by norm_num) hpos
  have hR : digitReversal a = Nat.ofDigits 10 (Nat.digits 10 (a / 10)).reverse
      + 10 ^ (Nat.digits 10 (a / 10)).length * (a % 10) := by
    unfold digitReversal
    rw [hd, List.reverse_cons, Nat.ofDigits_append, Nat.ofDigits_singleton, List.length_reverse]
  have hlt : a < 10 ^ ((Nat.digits 10 (a / 10)).length + 1) := by
    have h := Nat.lt_base_pow_length_digits (b := 10) (m := a) (by norm_num)
    rw [hd, List.length_cons] at h
    exact h
  have hge : 10 ^ (Nat.digits 10 (a / 10)).length ≤ digitReversal a := by
    rw [hR]
    have h1 : 1 ≤ a % 10 := by omega
    calc 10 ^ (Nat.digits 10 (a / 10)).length
        = 10 ^ (Nat.digits 10 (a / 10)).length * 1 := (mul_one _).symm
      _ ≤ 10 ^ (Nat.digits 10 (a / 10)).length * (a % 10) := Nat.mul_le_mul_left _ h1
      _ ≤ _ := Nat.le_add_left _ _
  apply Nat.div_lt_of_lt_mul
  calc a < 10 ^ ((Nat.digits 10 (a / 10)).length + 1) := hlt
    _ = 10 ^ (Nat.digits 10 (a / 10)).length * 10 := pow_succ _ _
    _ ≤ digitReversal a * 10 := Nat.mul_le_mul_right _ hge

lemma rev1 (a : ℕ) (h0 : 0 < a) (h : a < 10) : digitReversal a = a := by
  unfold digitReversal
  rw [Nat.digits_of_lt 10 a (by omega) h]
  simp

lemma rev2 (a : ℕ) (h0 : 10 ≤ a) (h : a < 100) : digitReversal a = a % 10 * 10 + a / 10 := by
  unfold digitReversal
  rw [Nat.digits_def' (by norm_num) (by omega), Nat.digits_of_lt 10 (a / 10) (by omega) (by omega)]
  simp [Nat.ofDigits]
  omega

lemma rev3 (a : ℕ) (h0 : 100 ≤ a) (h : a < 1000) :
    digitReversal a = a % 10 * 100 + a / 10 % 10 * 10 + a / 10 / 10 := by
  unfold digitReversal
  rw [Nat.digits_def' (by norm_num) (by omega), Nat.digits_def' (by norm_num) (by omega),
    Nat.digits_of_lt 10 (a / 10 / 10) (by omega) (by omega)]
  simp [Nat.ofDigits]
  omega

lemma ar2 (t z : ℕ) (hz : 1 ≤ z) (ht : t ≤ 9) (h : 5 * (z * 10 + t) ≤ 10 * t + z) : False := by
  omega

lemma ar3 (x y z : ℕ) (hz : 1 ≤ z) (h : 5 * (z * 100 + y * 10 + x) ≤ 100 * x + 10 * y + z) :
    601 ≤ 100 * x + 10 * y + z := by
  have h1 : 499 * z + 40 * y ≤ 95 * x := by omega
  have h2 : 499 ≤ 95 * x := by nlinarith
  have h3 : 6 ≤ x := by omega
  omega

lemma ar9 (x y z : ℕ) (hz : 1 ≤ z) (hx : x ≤ 9)
    (h : 9 * (z * 100 + y * 10 + x) ≤ 100 * x + 10 * y + z) : False := by
  omega

lemma small (a n : ℕ) (hpos : 0 < a) (hmod : a % 10 ≠ 0) (h1000 : a < 1000)
    (hq : a / digitReversal a = n) (hn : 5 ≤ n) : 601 ≤ a ∧ n ≤ 8 := by
  have h1 : a / digitReversal a * digitReversal a ≤ a := Nat.div_mul_le_self a _
  rw [hq] at h1
  have key : ∀ c, c ≤ n → c * digitReversal a ≤ a := fun c hc =>
    le_trans (Nat.mul_le_mul_right _ hc) h1
  have k5 := key 5 hn
  rcases (show a < 10 ∨ (10 ≤ a ∧ a < 100) ∨ 100 ≤ a by omega) with h | ⟨h, h'⟩ | h
  · rw [rev1 a hpos h] at k5
    omega
  · rw [rev2 a h h'] at k5
    exact (ar2 (a / 10) (a % 10) (by omega) (by omega) (by omega)).elim
  · rw [rev3 a h h1000] at k5
    have h601 := ar3 (a / 10 / 10) (a / 10 % 10) (a % 10) (by omega) (by omega)
    refine ⟨by omega, ?_⟩
    by_contra h9
    have k9 := key 9 (by omega)
    rw [rev3 a h h1000] at k9
    exact ar9 (a / 10 / 10) (a / 10 % 10) (a % 10) (by omega) (by omega) (by omega)

lemma mem_w (w n : ℕ) (h1 : 100 ≤ w) (h2 : w < 1000)
    (h : w / (w % 10 * 100 + w / 10 % 10 * 10 + w / 10 / 10) = n) :
    w ∈ {k : ℕ | 0 < k ∧ k / digitReversal k = n} := by
  refine ⟨by omega, ?_⟩
  rw [rev3 w h1 h2]
  exact h

end A068779Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a068779.main := by
  intro n a hn hterm
  obtain ⟨⟨hpos, hq⟩, hleast⟩ := hterm
  by_contra hdiv
  have hmod : a % 10 ≠ 0 := fun h => hdiv (Nat.dvd_of_mod_eq_zero h)
  have hlt := A068779Proof.quot_lt_ten a hpos hmod
  rw [hq] at hlt
  have hw : a ≤ 890 ∧ (n ≤ 8 → a ≤ 450) := by
    interval_cases n
    · have h := hleast (A068779Proof.mem_w 120 5 (by norm_num) (by norm_num) (by norm_num))
      omega
    · have h := hleast (A068779Proof.mem_w 350 6 (by norm_num) (by norm_num) (by norm_num))
      omega
    · have h := hleast (A068779Proof.mem_w 230 7 (by norm_num) (by norm_num) (by norm_num))
      omega
    · have h := hleast (A068779Proof.mem_w 450 8 (by norm_num) (by norm_num) (by norm_num))
      omega
    · have h := hleast (A068779Proof.mem_w 890 9 (by norm_num) (by norm_num) (by norm_num))
      omega
  have hs := A068779Proof.small a n hpos hmod (by omega) hq hn
  omega
