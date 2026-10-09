import RequestProject.Erdos287.Window

/-!
# Erdős #287 — effective one-prime finisher (V103 track, arithmetic part)

**ERDŐS #287 REMAINS OPEN.**  This module is independent of the Type-II / Pascadi development.

* `Counterexample287 M` — the actual counterexample predicate: a finite set of distinct
  denominators `≥ 2`, reciprocal sum `1`, maximum `M`, and every consecutive gap `≤ 2` (the
  next element after any `a < M` is at most `a + 2`).
* `Lh h = lcm(1,…,h)`, `Bh h = ∑_{j ≤ h} L_h / j`, `Hstar M = max {h ≤ M : h B_h < M}`.
* `num_le_Bh` — every reciprocal sum over a nonempty `S ⊆ {1,…,j}` has reduced numerator
  `≤ B_j`; `C_le_Bh` — hence `C(j) ≤ B_j`.
* `row_empty` — **`q`-adic row emptiness**: if `q` is prime and `B_{⌊M/q⌋} < q` then no
  denominator is divisible by `q`.
* `one_prime_finisher` — `h B_h < M`, `p` prime, `M/2 < p ≤ M`, `q` prime,
  `p + 1 = a q` or `p - 1 = a q`, `a ≤ ⌊(h-1)/2⌋` ⟹ `¬ Counterexample287 M`.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Effective

/-- `L_h = lcm(1, …, h)`. -/
def Lh (h : ℕ) : ℕ := (Icc 1 h).lcm id

/-- `B_h = ∑_{j=1}^{h} L_h / j`. -/
def Bh (h : ℕ) : ℕ := ∑ j ∈ Icc 1 h, Lh h / j

/-- The maximal uniform height `H_*(M) = max {h : h B_h < M}` (search range `h ≤ M`; every
`h` with `h B_h < M`, `h ≥ 1`, satisfies `h < M`). -/
def Hstar (M : ℕ) : ℕ := Nat.findGreatest (fun h => h * Bh h < M) M

/-- **The counterexample predicate** for Erdős #287 with all consecutive gaps `≤ 2`. -/
def Counterexample287 (M : ℕ) : Prop :=
  ∃ A : Finset ℕ, (∀ a ∈ A, 2 ≤ a) ∧ (∑ a ∈ A, (1 : ℚ) / a = 1) ∧ M ∈ A ∧ (∀ a ∈ A, a ≤ M) ∧
    ∀ a ∈ A, a < M → ∃ b ∈ A, a < b ∧ b ≤ a + 2

/-! ### `L_h`, `B_h` -/

lemma Lh_pos (h : ℕ) : 0 < Lh h := by
  unfold Lh
  refine Nat.pos_of_ne_zero (fun h0 => ?_)
  obtain ⟨x, hx, hx0⟩ := Finset.lcm_eq_zero_iff.1 h0
  simp only [mem_Icc, id] at hx hx0; omega

lemma dvd_Lh {j h : ℕ} (hj : j ∈ Icc 1 h) : j ∣ Lh h := Finset.dvd_lcm hj

lemma Lh_dvd_Lh {j h : ℕ} (hjh : j ≤ h) : Lh j ∣ Lh h :=
  Finset.lcm_mono (Icc_subset_Icc_right hjh)

lemma Bh_mono {j h : ℕ} (hjh : j ≤ h) : Bh j ≤ Bh h := by
  unfold Bh
  have hL : Lh j ≤ Lh h := Nat.le_of_dvd (Lh_pos h) (Lh_dvd_Lh hjh)
  calc ∑ i ∈ Icc 1 j, Lh j / i ≤ ∑ i ∈ Icc 1 j, Lh h / i :=
        sum_le_sum (fun i _ => Nat.div_le_div_right hL)
    _ ≤ ∑ i ∈ Icc 1 h, Lh h / i :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hjh) (fun _ _ _ => Nat.zero_le _)

lemma one_le_Bh {h : ℕ} (hh : 1 ≤ h) : 1 ≤ Bh h := by
  unfold Bh
  have h1 : (1 : ℕ) ∈ Icc 1 h := mem_Icc.2 ⟨le_rfl, hh⟩
  calc 1 ≤ Lh h / 1 := by rw [Nat.div_one]; exact Lh_pos h
    _ ≤ ∑ i ∈ Icc 1 h, Lh h / i := single_le_sum (fun _ _ => Nat.zero_le _) h1

theorem Bh_values : Bh 1 = 1 ∧ Bh 2 = 3 ∧ Bh 3 = 11 ∧ Bh 4 = 25 ∧ Bh 5 = 137 ∧ Bh 6 = 147 ∧
    Bh 7 = 1089 ∧ Bh 8 = 2283 ∧ Bh 9 = 7129 ∧ Bh 10 = 7381 ∧ Bh 11 = 83711 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Every reciprocal sum over a nonempty `S ⊆ {1,…,j}` has reduced numerator `≤ B_j`. -/
theorem num_le_Bh (j : ℕ) (S : Finset ℕ) (hne : S.Nonempty) (hsub : S ⊆ Icc 1 j) :
    (∑ s ∈ S, (1 : ℚ) / s).num ≤ Bh j := by
  set L := Lh j with hL
  set K : ℕ := ∑ s ∈ S, L / s with hK
  have hpos : ∀ s ∈ S, 0 < s := fun s hs => (mem_Icc.1 (hsub hs)).1
  have hLpos : (0 : ℚ) < L := by exact_mod_cast Lh_pos j
  have hsum : ∑ s ∈ S, (1 : ℚ) / s = (K : ℚ) / L := by
    rw [hK, Nat.cast_sum, sum_div]
    refine sum_congr rfl (fun s hs => ?_)
    rw [Nat.cast_div (dvd_Lh (hsub hs)) (by exact_mod_cast (hpos s hs).ne')]
    field_simp
    try rfl
  have hKpos : 0 < K := by
    obtain ⟨s, hs⟩ := hne
    refine lt_of_lt_of_le ?_ (single_le_sum (f := fun s => L / s) (fun _ _ => Nat.zero_le _) hs)
    exact Nat.div_pos (Nat.le_of_dvd (Lh_pos j) (dvd_Lh (hsub hs))) (hpos s hs)
  have hdiv : (∑ s ∈ S, (1 : ℚ) / s) = Rat.divInt K L := by
    rw [hsum, Rat.divInt_eq_div]; push_cast; rfl
  have hnum_dvd : (∑ s ∈ S, (1 : ℚ) / s).num ∣ (K : ℤ) := by
    rw [hdiv]; exact Rat.num_dvd _ (by exact_mod_cast (Lh_pos j).ne')
  have hnum_le : (∑ s ∈ S, (1 : ℚ) / s).num ≤ K :=
    Int.le_of_dvd (by exact_mod_cast hKpos) hnum_dvd
  refine hnum_le.trans ?_
  have : K ≤ Bh j := by
    unfold Bh
    exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  exact_mod_cast this

/-- `C(j) ≤ B_j`. -/
theorem C_le_Bh (j : ℕ) : C j ≤ Bh j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · decide
  obtain ⟨S, hne, hsub, hval⟩ := C_attained j hj
  rw [← hval]; exact num_le_Bh j S hne hsub

/-- **`q`-adic row emptiness.** -/
theorem row_empty (A : Finset ℕ) (M q : ℕ) (hq : q.Prime) (hpos : ∀ a ∈ A, 0 < a)
    (hAM : ∀ a ∈ A, a ≤ M) (hsum : ∑ a ∈ A, (1 : ℚ) / a = 1) (hB : Bh (M / q) < q) :
    ∀ a ∈ A, ¬ q ∣ a := by
  by_cases hqM : q ≤ M
  · have h := primePower_window_exclusion A M q 1 hq hpos hAM hsum le_rfl (by simpa using hqM)
      (by rw [pow_one]; exact lt_of_le_of_lt (C_le_Bh _) (by exact_mod_cast hB))
    simpa using h
  · intro a ha hd
    have := Nat.le_of_dvd (hpos a ha) hd
    have := hAM a ha
    omega

/-- **Effective one-prime finisher.** -/
theorem one_prime_finisher (M h p q a : ℕ) (hhB : h * Bh h < M) (hp : p.Prime)
    (hp1 : M < 2 * p) (hp2 : p ≤ M) (hq : q.Prime) (haq : p + 1 = a * q ∨ p - 1 = a * q)
    (hah : a ≤ (h - 1) / 2) : ¬ Counterexample287 M := by
  rintro ⟨A, h2, hsum, hMA, hAM, hgap⟩
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => by have := h2 a ha; omega
  -- `p ∉ A`: the `p`-row is empty (`⌊M/p⌋ = 1`, `B_1 = 1 < p`)
  have hMp : M / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hpA : p ∉ A := by
    intro hpa
    have := row_empty A M p hp hpos hAM hsum (by rw [hMp, show Bh 1 = 1 by decide]; exact hp.one_lt) p hpa
    exact this dvd_rfl
  -- some denominator is below `p`
  have hbelow : ∃ b ∈ A, b < p := by
    by_contra hcon
    push_neg at hcon
    have hge : ∀ b ∈ A, p + 1 ≤ b := fun b hb =>
      lt_of_le_of_ne (hcon b hb) (fun he => hpA (he ▸ hb))
    have hsub : A ⊆ Icc (p + 1) M := fun b hb => mem_Icc.2 ⟨hge b hb, hAM b hb⟩
    have hle : ∑ b ∈ A, (1 : ℚ) / b ≤ ∑ b ∈ A, (1 : ℚ) / (p + 1) :=
      sum_le_sum (fun b hb => by
        have : ((p : ℚ) + 1) ≤ b := by exact_mod_cast hge b hb
        exact one_div_le_one_div_of_le (by positivity) this)
    rw [sum_const, nsmul_eq_mul] at hle
    have hcard : (A.card : ℚ) ≤ M - p := by
      have hc := card_le_card hsub
      rw [Nat.card_Icc] at hc
      have hc' : A.card ≤ M - p := by omega
      have : ((A.card : ℕ) : ℚ) ≤ ((M - p : ℕ) : ℚ) := by exact_mod_cast hc'
      rwa [Nat.cast_sub hp2] at this
    have : (A.card : ℚ) * (1 / (p + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      have : (M : ℚ) < 2 * p := by exact_mod_cast hp1
      linarith
    linarith
  -- the largest denominator below `p` is `p - 1`, and then `p + 1 ∈ A`
  classical
  set Bset := A.filter (· < p) with hBset
  have hBne : Bset.Nonempty := by
    obtain ⟨b, hb, hbp⟩ := hbelow; exact ⟨b, mem_filter.2 ⟨hb, hbp⟩⟩
  set a' := Bset.max' hBne with ha'
  have ha'mem := mem_filter.1 (Bset.max'_mem hBne)
  have ha'max : ∀ b ∈ A, b < p → b ≤ a' := fun b hb hbp =>
    Bset.le_max' b (mem_filter.2 ⟨hb, hbp⟩)
  obtain ⟨b, hbA, hab, hb2⟩ := hgap a' ha'mem.1 (by omega)
  have hbp : p ≤ b := by
    by_contra hlt; push_neg at hlt; have := ha'max b hbA hlt; omega
  have hbp' : b ≠ p := fun he => hpA (he ▸ hbA)
  have hpm1 : p - 1 ∈ A := by
    have : a' = p - 1 := by omega
    rw [← this]; exact ha'mem.1
  have hpp1 : p + 1 ∈ A := by
    have : b = p + 1 := by omega
    rw [← this]; exact hbA
  -- the element `a q = p ± 1` lies in `A`
  have haqA : a * q ∈ A := by
    rcases haq with h' | h'
    · rw [← h']; exact hpp1
    · rw [← h']; exact hpm1
  -- `B_{⌊M/q⌋} < q`
  have hq2 := hq.two_le
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, zero_mul] at haq; have := hp.two_le; omega
    · exact h0
  have hh3 : 3 ≤ h := by
    have : 1 ≤ (h - 1) / 2 := le_trans ha1 hah
    omega
  have h2a : 2 * a ≤ h - 1 := by omega
  have haqge : M ≤ 2 * (a * q) + 1 := by rcases haq with h' | h' <;> omega
  have hj : M / q ≤ 2 * a := by
    calc M / q ≤ (2 * (a * q) + 1) / q := Nat.div_le_div_right haqge
      _ = 2 * a := by
        rw [show 2 * (a * q) + 1 = 1 + q * (2 * a) by ring, Nat.add_mul_div_left _ _ hq.pos,
          Nat.div_eq_of_lt (by omega), zero_add]
  have hBj : Bh (M / q) ≤ Bh h := Bh_mono (by omega)
  have hBh1 : 1 ≤ Bh h := one_le_Bh (by omega)
  have hqB : Bh h < q := by
    by_contra hle; push_neg at hle
    -- `h B_h < M ≤ 2 a q + 1 ≤ (h - 1) q + 1 ≤ (h - 1) B_h + 1`
    have hm : 2 * a * q ≤ (h - 1) * q := Nat.mul_le_mul_right q h2a
    have h1 : M ≤ (h - 1) * q + 1 := by
      have : 2 * (a * q) = 2 * a * q := by ring
      omega
    have h2 : (h - 1) * q ≤ (h - 1) * Bh h := Nat.mul_le_mul_left _ hle
    have h3 : h * Bh h = (h - 1) * Bh h + Bh h := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ h)]
    omega
  exact row_empty A M q hq hpos hAM hsum (lt_of_le_of_lt hBj hqB) (a * q) haqA
    (dvd_mul_left q a)

end Erdos287.Effective
