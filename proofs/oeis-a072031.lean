import OMAStatements.S_oeis_a072031
import Mathlib

namespace A072031
open OMA.S_oeis_a072031

def S (n : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (Finset.Icc 1 n).sigma (fun k => k.divisors ×ˢ (n - k).divisors)

def T (n : ℕ) : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
  n.divisors.sigma (fun d => (Finset.Icc 1 d).sigma (fun k => (k * (d - k)).divisors))

def phi (n : ℕ) (s : Σ _ : ℕ, ℕ × ℕ) : Σ _ : ℕ, Σ _ : ℕ, ℕ :=
  ⟨n / Nat.gcd (s.1 / s.2.1) s.2.2,
    ⟨s.1 / Nat.gcd (s.1 / s.2.1) s.2.2, s.2.1 * (s.2.2 / Nat.gcd (s.1 / s.2.1) s.2.2)⟩⟩

def psi (n : ℕ) (t : Σ _ : ℕ, Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ × ℕ :=
  ⟨n / t.1 * t.2.1, (Nat.gcd t.2.2 t.2.1, n / t.1 * (t.2.2 / Nat.gcd t.2.2 t.2.1))⟩

lemma mem_S (n k x y : ℕ) : (⟨k, (x, y)⟩ : Σ _ : ℕ, ℕ × ℕ) ∈ S n ↔
    (1 ≤ k ∧ k ≤ n) ∧ (x ∣ k ∧ k ≠ 0) ∧ (y ∣ n - k ∧ n - k ≠ 0) := by
  simp only [S, Finset.mem_sigma, Finset.mem_product, Finset.mem_Icc, Nat.mem_divisors]

lemma mem_T (n d k z : ℕ) : (⟨d, ⟨k, z⟩⟩ : Σ _ : ℕ, Σ _ : ℕ, ℕ) ∈ T n ↔
    (d ∣ n ∧ n ≠ 0) ∧ (1 ≤ k ∧ k ≤ d) ∧ (z ∣ k * (d - k) ∧ k * (d - k) ≠ 0) := by
  simp only [T, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]

lemma L1 (z A B : ℕ) (hA : 0 < A) (h : z ∣ A * B) : z / Nat.gcd z A ∣ B := by
  have hc : 0 < Nat.gcd z A := Nat.gcd_pos_of_pos_right z hA
  have hcop : Nat.Coprime (z / Nat.gcd z A) (A / Nat.gcd z A) := Nat.coprime_div_gcd_div_gcd hc
  apply hcop.dvd_of_dvd_mul_left
  have h1 : Nat.gcd z A * (z / Nat.gcd z A) = z := Nat.mul_div_cancel' (Nat.gcd_dvd_left z A)
  have h2 : Nat.gcd z A * (A / Nat.gcd z A) = A := Nat.mul_div_cancel' (Nat.gcd_dvd_right z A)
  apply Nat.dvd_of_mul_dvd_mul_left hc
  rw [h1, ← Nat.mul_assoc, h2]
  exact h

lemma fwd_core (n k x y g : ℕ) (hk : 1 ≤ k) (hkn : k < n) (hx : x ∣ k) (hy : y ∣ n - k)
    (hg1 : g ∣ k / x) (hg2 : g ∣ y) (hgpos : 0 < g) :
    g ∣ n ∧ 1 ≤ k / g ∧ k / g ≤ n / g ∧ x * (y / g) ∣ k / g * (n / g - k / g) ∧
      k / g * (n / g - k / g) ≠ 0 := by
  have hx0 : 0 < x := Nat.pos_of_dvd_of_pos hx hk
  obtain ⟨x', rfl⟩ := hx
  rw [Nat.mul_div_cancel_left x' hx0] at hg1
  obtain ⟨p, rfl⟩ := hg1
  obtain ⟨q, rfl⟩ := hg2
  obtain ⟨y', hy'⟩ := hy
  have hn : n = g * (x * p + q * y') := by
    have h1 : n = x * (g * p) + g * q * y' := by omega
    rw [h1]
    ring
  subst hn
  have e1 : x * (g * p) / g = x * p := by
    rw [show x * (g * p) = g * (x * p) by ring]
    exact Nat.mul_div_cancel_left _ hgpos
  have e2 : g * (x * p + q * y') / g = x * p + q * y' := Nat.mul_div_cancel_left _ hgpos
  have e3 : g * q / g = q := Nat.mul_div_cancel_left _ hgpos
  have e4 : x * p + q * y' - x * p = q * y' := by omega
  rw [e1, e2, e3, e4]
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h
      simp at hk
    · exact h
  have hqy : 0 < q * y' := by
    rcases Nat.eq_zero_or_pos (q * y') with h | h
    · rw [h] at hkn
      have h2 : g * (x * p + 0) = x * (g * p) := by ring
      omega
    · exact h
  refine ⟨Dvd.intro _ rfl, Nat.mul_pos hx0 hp0, Nat.le_add_right _ _, ⟨p * y', by ring⟩, ?_⟩
  exact Nat.mul_ne_zero (Nat.mul_pos hx0 hp0).ne' hqy.ne'

lemma bwd_core (d g k z : ℕ) (hg : 0 < g) (hk1 : 1 ≤ k) (hkd : k < d)
    (hz : z ∣ k * (d - k)) :
    (1 ≤ g * k ∧ g * k ≤ d * g) ∧ (Nat.gcd z k ∣ g * k ∧ g * k ≠ 0) ∧
      (g * (z / Nat.gcd z k) ∣ d * g - g * k ∧ d * g - g * k ≠ 0) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = k + e := ⟨d - k, by omega⟩
  have he : 0 < e := by omega
  rw [Nat.add_sub_cancel_left] at hz
  have h2 : (k + e) * g = g * k + g * e := by ring
  have h1 : (k + e) * g - g * k = g * e := by omega
  rw [h1]
  refine ⟨⟨Nat.mul_pos hg hk1, by omega⟩,
    ⟨Dvd.dvd.mul_left (Nat.gcd_dvd_right z k) g, (Nat.mul_pos hg hk1).ne'⟩,
    ⟨Nat.mul_dvd_mul_left g (L1 z k e hk1 hz), (Nat.mul_pos hg he).ne'⟩⟩

lemma left_core (n k x y g : ℕ) (hk : 1 ≤ k) (hkn : k < n) (hx : x ∣ k) (hy : y ∣ n - k)
    (hg1 : g ∣ k / x) (hg2 : g ∣ y) (hcop : Nat.Coprime (k / x / g) (y / g)) :
    n / (n / g) * (k / g) = k ∧ Nat.gcd (x * (y / g)) (k / g) = x ∧
      n / (n / g) * (x * (y / g) / Nat.gcd (x * (y / g)) (k / g)) = y := by
  have hx0 : 0 < x := Nat.pos_of_dvd_of_pos hx hk
  have hgk : g ∣ k := dvd_trans hg1 (Nat.div_dvd_of_dvd hx)
  have hgn : g ∣ n := by
    have h := dvd_add hgk (dvd_trans hg2 hy)
    rwa [Nat.add_sub_of_le hkn.le] at h
  have ha : n / (n / g) = g := Nat.div_div_self hgn (by omega)
  have hb : g * (k / g) = k := Nat.mul_div_cancel' hgk
  have hkg : k / g = x * (k / x / g) := by
    have h1 : x * (k / x) = k := Nat.mul_div_cancel' hx
    calc k / g = x * (k / x) / g := by rw [h1]
      _ = x * (k / x / g) := Nat.mul_div_assoc x hg1
  have hc : Nat.gcd (x * (y / g)) (k / g) = x := by
    rw [hkg, Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hcop.symm, Nat.mul_one]
  refine ⟨by rw [ha, hb], hc, ?_⟩
  rw [ha, hc, Nat.mul_div_cancel_left _ hx0, Nat.mul_div_cancel' hg2]

lemma right_core (n d k z : ℕ) (hd : d ∣ n) (hn : n ≠ 0) (hk1 : 1 ≤ k) :
    n / Nat.gcd (n / d * k / Nat.gcd z k) (n / d * (z / Nat.gcd z k)) = d ∧
    n / d * k / Nat.gcd (n / d * k / Nat.gcd z k) (n / d * (z / Nat.gcd z k)) = k ∧
    Nat.gcd z k * (n / d * (z / Nat.gcd z k) /
      Nat.gcd (n / d * k / Nat.gcd z k) (n / d * (z / Nat.gcd z k))) = z := by
  have hc : 0 < Nat.gcd z k := Nat.gcd_pos_of_pos_right z hk1
  have hcop : Nat.Coprime (z / Nat.gcd z k) (k / Nat.gcd z k) := Nat.coprime_div_gcd_div_gcd hc
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn)
  have hG : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hd0
  have e1 : n / d * k / Nat.gcd z k = n / d * (k / Nat.gcd z k) :=
    Nat.mul_div_assoc _ (Nat.gcd_dvd_right z k)
  have e2 : Nat.gcd (n / d * (k / Nat.gcd z k)) (n / d * (z / Nat.gcd z k)) = n / d := by
    rw [Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hcop.symm, Nat.mul_one]
  rw [e1, e2]
  refine ⟨Nat.div_div_self hd hn, Nat.mul_div_cancel_left k hG, ?_⟩
  rw [Nat.mul_div_cancel_left _ hG, Nat.mul_div_cancel' (Nat.gcd_dvd_left z k)]

lemma phi_mem (n : ℕ) : ∀ s ∈ S n, phi n s ∈ T n := by
  rintro ⟨k, x, y⟩ hs
  rw [mem_S] at hs
  obtain ⟨⟨hk1, hkn⟩, ⟨hxk, _⟩, ⟨hy, hnk⟩⟩ := hs
  have hy0 : 0 < y := Nat.pos_of_dvd_of_pos hy (Nat.pos_of_ne_zero hnk)
  have hgpos : 0 < Nat.gcd (k / x) y := Nat.gcd_pos_of_pos_right _ hy0
  obtain ⟨h1, h3, h4, h5, h6⟩ := fwd_core n k x y (Nat.gcd (k / x) y) hk1 (by omega) hxk hy
    (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) hgpos
  show (⟨n / Nat.gcd (k / x) y, ⟨k / Nat.gcd (k / x) y, x * (y / Nat.gcd (k / x) y)⟩⟩ :
    Σ _ : ℕ, Σ _ : ℕ, ℕ) ∈ T n
  rw [mem_T]
  exact ⟨⟨Nat.div_dvd_of_dvd h1, by omega⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩

lemma psi_mem (n : ℕ) : ∀ t ∈ T n, psi n t ∈ S n := by
  rintro ⟨d, k, z⟩ ht
  rw [mem_T] at ht
  obtain ⟨⟨hdn, hn0⟩, ⟨hk1, hkd⟩, ⟨hz, hne⟩⟩ := ht
  have hkd' : k < d := by
    rcases Nat.lt_or_ge k d with h | h
    · exact h
    · have h0 : d - k = 0 := by omega
      rw [h0] at hne
      simp at hne
  obtain ⟨G, rfl⟩ := hdn
  have hd0 : 0 < d := by omega
  have hGpos : 0 < G := by
    rcases Nat.eq_zero_or_pos G with h | h
    · subst h
      simp at hn0
    · exact h
  have hG : d * G / d = G := Nat.mul_div_cancel_left G hd0
  show (⟨d * G / d * k, (Nat.gcd z k, d * G / d * (z / Nat.gcd z k))⟩ : Σ _ : ℕ, ℕ × ℕ) ∈
    S (d * G)
  rw [hG, mem_S]
  exact bwd_core d G k z hGpos hk1 hkd' hz

lemma left_inv (n : ℕ) : ∀ s ∈ S n, psi n (phi n s) = s := by
  rintro ⟨k, x, y⟩ hs
  rw [mem_S] at hs
  obtain ⟨⟨hk1, hkn⟩, ⟨hxk, _⟩, ⟨hy, hnk⟩⟩ := hs
  have hy0 : 0 < y := Nat.pos_of_dvd_of_pos hy (Nat.pos_of_ne_zero hnk)
  have hgpos : 0 < Nat.gcd (k / x) y := Nat.gcd_pos_of_pos_right _ hy0
  obtain ⟨h1, h2, h3⟩ := left_core n k x y (Nat.gcd (k / x) y) hk1 (by omega) hxk hy
    (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) (Nat.coprime_div_gcd_div_gcd hgpos)
  exact Sigma.ext h1 (heq_of_eq (Prod.ext h2 h3))

lemma right_inv (n : ℕ) : ∀ t ∈ T n, phi n (psi n t) = t := by
  rintro ⟨d, k, z⟩ ht
  rw [mem_T] at ht
  obtain ⟨⟨hdn, hn0⟩, ⟨hk1, _⟩, _⟩ := ht
  obtain ⟨r1, r2, r3⟩ := right_core n d k z hdn hn0 hk1
  exact Sigma.ext r1 (heq_of_eq (Sigma.ext r2 (heq_of_eq r3)))

end A072031

theorem OMA.solution : type_of% @OMA.S_oeis_a072031.main := by
  intro n _
  have hL : ∑ k ∈ Finset.Icc 1 n, OMA.S_oeis_a072031.tau k * OMA.S_oeis_a072031.tau (n - k)
      = (A072031.S n).card := by
    unfold A072031.S
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro k _
    show OMA.S_oeis_a072031.tau k * OMA.S_oeis_a072031.tau (n - k)
      = (k.divisors ×ˢ (n - k).divisors).card
    rw [Finset.card_product]
    rfl
  have hR : ∑ d ∈ n.divisors, ∑ k ∈ Finset.Icc 1 d, OMA.S_oeis_a072031.tau (k * (d - k))
      = (A072031.T n).card := by
    unfold A072031.T
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro d _
    show ∑ k ∈ Finset.Icc 1 d, OMA.S_oeis_a072031.tau (k * (d - k))
      = ((Finset.Icc 1 d).sigma (fun k => (k * (d - k)).divisors)).card
    rw [Finset.card_sigma]
    rfl
  rw [hL, hR]
  exact Finset.card_nbij' (A072031.phi n) (A072031.psi n)
    (fun a ha => Finset.mem_coe.2 (A072031.phi_mem n a (Finset.mem_coe.1 ha)))
    (fun a ha => Finset.mem_coe.2 (A072031.psi_mem n a (Finset.mem_coe.1 ha)))
    (fun a ha => A072031.left_inv n a (Finset.mem_coe.1 ha))
    (fun a ha => A072031.right_inv n a (Finset.mem_coe.1 ha))
