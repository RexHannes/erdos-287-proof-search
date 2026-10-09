import RequestProject.Erdos287.QSigma.Source

/-!
# Erdős #287 — post-`Q_Σ` bank, §9 A–B and §13 (V57/V58): raw-source normalisations

**Status: BANK (proved in Lean).**

For the raw source (`R = ∅`) with harmonic mass `H(a,M) = ∑_{n=a}^{M} 1/n`:

* `harmonic_source_le_half` — `H(a,M) ≥ 1` and `a > 1` ⇒ `a ≤ ⌊M/2⌋`;
* `lcm_Icc_eq_lcm_one` — `2a ≤ M + 2` ⇒ `lcm(a,…,M) = lcm(1,…,M)`;
  `W_raw_eq_lcm_one` — the same for the source modulus `W a M ∅`;
* `harmonic_lt_log` — `H(a,M) < log M - log (a-1)` (`2 ≤ a ≤ M`);
* `exp_mul_pred_lt_of_harmonic` — the upper corridor `e·(a-1) < M` from `H(a,M) ≥ 1`;
* `eight_mul_pred_lt_three_mul` — its rational consequence `8(a-1) < 3M`, i.e. `a - 1 < 3M/8`.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

/-- Harmonic mass of the interval `[a, M]`. -/
def Hm (a M : ℕ) : ℚ := ∑ n ∈ Finset.Icc a M, (1 : ℚ) / n

/-- For the raw source, `τ = H(a,M) - 1`. -/
theorem tau_raw_eq {a M : ℕ} (ha : 0 < a) : tau a M ∅ = Hm a M - 1 := by
  rw [tau_eq ha, Hm, B, Finset.sdiff_empty]

/-- **V57 A (harmonic source)**: `H(a, M) ≥ 1`, `a > 1` ⇒ `a ≤ ⌊M/2⌋`. -/
theorem harmonic_source_le_half {a M : ℕ} (ha : 1 < a) (hH : 1 ≤ Hm a M) : a ≤ M / 2 := by
  by_contra hc
  push_neg at hc
  have h2a : M + 1 ≤ 2 * a := by omega
  rcases lt_or_ge M a with hMa | haM
  · have : Finset.Icc a M = ∅ := Finset.Icc_eq_empty (by omega)
    rw [Hm, this] at hH; simp at hH; linarith
  have haq : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
  -- split off the top term `1/M`
  have hsplit : Finset.Icc a M = insert M (Finset.Icc a (M - 1)) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : M ∉ Finset.Icc a (M - 1) := by simp only [Finset.mem_Icc]; omega
  rw [Hm, hsplit, Finset.sum_insert hnot] at hH
  have hrest : ∑ n ∈ Finset.Icc a (M - 1), (1 : ℚ) / n ≤ (M - a : ℕ) * (1 / a) := by
    have := Finset.sum_le_card_nsmul (Finset.Icc a (M - 1)) (fun n => (1 : ℚ) / n) (1 / a)
      (fun n hn => by
        have hn' := (Finset.mem_Icc.1 hn).1
        have : (a : ℚ) ≤ n := by exact_mod_cast hn'
        exact one_div_le_one_div_of_le haq this)
    rw [Nat.card_Icc, nsmul_eq_mul] at this
    have e : M - 1 + 1 - a = M - a := by omega
    rw [e] at this; exact this
  rcases eq_or_lt_of_le haM with rfl | hlt
  · have : Finset.Icc a (a - 1) = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this] at hH; simp at hH
    have : (1 : ℚ) < a := by exact_mod_cast ha
    rw [inv_eq_one_div, le_div_iff₀ haq] at hH; linarith
  · have hM : (1 : ℚ) / M < 1 / a := by
      apply one_div_lt_one_div_of_lt haq; exact_mod_cast hlt
    have hcast : ((M - a : ℕ) : ℚ) = (M : ℚ) - a := by
      rw [Nat.cast_sub hlt.le]
    rw [hcast] at hrest
    have hkey : (1 : ℚ) / a + ((M : ℚ) - a) * (1 / a) = ((M : ℚ) + 1 - a) / a := by
      field_simp; ring
    have hle : ((M : ℚ) + 1 - a) / a ≤ 1 := by
      rw [div_le_one haq]
      have : ((M + 1 : ℕ) : ℚ) ≤ ((2 * a : ℕ) : ℚ) := by exact_mod_cast h2a
      push_cast at this; linarith
    linarith

/-- **V57 B (LCM normalisation)**: if `2a ≤ M + 2` then `lcm(a,…,M) = lcm(1,…,M)`. -/
theorem lcm_Icc_eq_lcm_one {a M : ℕ} (ha : 0 < a) (h : 2 * a ≤ M + 2) :
    (Finset.Icc a M).lcm id = (Finset.Icc 1 M).lcm id := by
  apply Nat.dvd_antisymm
  · exact Finset.lcm_mono (fun n hn => by
      simp only [Finset.mem_Icc] at hn ⊢; omega)
  · refine Finset.lcm_dvd (fun k hk => ?_)
    simp only [Finset.mem_Icc] at hk
    by_cases hka : a ≤ k
    · exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.2 ⟨hka, hk.2⟩)
    · push_neg at hka
      set m := k * ((a + k - 1) / k) with hm
      have hk0 : 0 < k := by omega
      have h1 : a ≤ m := by
        have := Nat.lt_div_mul_add (a := a + k - 1) hk0
        rw [hm, mul_comm]; omega
      have h2 : m ≤ a + k - 1 := by rw [hm, mul_comm]; exact Nat.div_mul_le_self _ _
      have hmem : m ∈ Finset.Icc a M := Finset.mem_Icc.2 ⟨h1, by omega⟩
      exact (Dvd.intro _ rfl).trans (Finset.dvd_lcm (f := id) hmem)

/-- The raw-source modulus is `lcm(1,…,M)` when `2a ≤ M + 2`. -/
theorem W_raw_eq_lcm_one {a M : ℕ} (ha : 0 < a) (h : 2 * a ≤ M + 2) :
    W a M ∅ = (Finset.Icc 1 M).lcm id := by
  rw [W, B, Finset.sdiff_empty, lcm_Icc_eq_lcm_one ha h]

/-! ## The harmonic corridor (upper side) -/

lemma one_div_lt_log_sub {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) / n < Real.log n - Real.log (n - 1) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  rw [← Real.log_div (by linarith) h1.ne']
  have key : Real.log (((n : ℝ) - 1) / n) < ((n : ℝ) - 1) / n - 1 :=
    Real.log_lt_sub_one_of_pos (by positivity) (by
      intro h; field_simp at h; linarith)
  have hinv : Real.log ((n : ℝ) / (n - 1)) = - Real.log (((n : ℝ) - 1) / n) := by
    rw [← Real.log_inv, inv_div]
  rw [hinv]
  have : ((n : ℝ) - 1) / n - 1 = -(1 / n) := by field_simp; ring
  linarith

/-- `H(a, M) < log M - log (a - 1)` for `2 ≤ a ≤ M`. -/
theorem harmonic_lt_log {a M : ℕ} (ha : 2 ≤ a) (haM : a ≤ M) :
    (∑ n ∈ Finset.Icc a M, (1 : ℝ) / n) < Real.log M - Real.log ((a : ℝ) - 1) := by
  induction M, haM using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton]
    exact one_div_lt_log_sub ha
  | succ b hb ih =>
    have hsplit : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : b + 1 ∉ Finset.Icc a b := by simp
    rw [hsplit, Finset.sum_insert hnot]
    have := one_div_lt_log_sub (n := b + 1) (by omega)
    push_cast at this ⊢
    simp only [add_sub_cancel_right] at this
    linarith

/-- **Upper harmonic corridor**: `H(a,M) ≥ 1` (with `a ≥ 2`) ⇒ `e·(a-1) < M`. -/
theorem exp_mul_pred_lt_of_harmonic {a M : ℕ} (ha : 2 ≤ a) (hH : 1 ≤ Hm a M) :
    Real.exp 1 * ((a : ℝ) - 1) < M := by
  have haM : a ≤ M := by
    by_contra hc; push_neg at hc
    rw [Hm, Finset.Icc_eq_empty (by omega)] at hH; simp at hH; linarith
  have h1 := harmonic_lt_log ha haM
  have hH' : (1 : ℝ) ≤ ∑ n ∈ Finset.Icc a M, (1 : ℝ) / n := by
    have : ((Hm a M : ℚ) : ℝ) = ∑ n ∈ Finset.Icc a M, (1 : ℝ) / n := by
      rw [Hm]; push_cast; rfl
    rw [← this]; exact_mod_cast hH
  have ha1 : (0 : ℝ) < (a : ℝ) - 1 := by
    have : (2 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  have hM : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlog : 1 < Real.log M - Real.log ((a : ℝ) - 1) := lt_of_le_of_lt hH' h1
  rw [← Real.log_div hM.ne' ha1.ne'] at hlog
  have := Real.exp_lt_exp.2 hlog
  rw [Real.exp_log (by positivity), lt_div_iff₀ ha1] at this
  linarith

/-- **Rational corridor consequence**: `H(a,M) ≥ 1` ⇒ `8(a-1) < 3M`, i.e. `a - 1 < 3M/8`. -/
theorem eight_mul_pred_lt_three_mul {a M : ℕ} (ha : 2 ≤ a) (hH : 1 ≤ Hm a M) :
    8 * (a - 1) < 3 * M := by
  have h := exp_mul_pred_lt_of_harmonic ha hH
  have he : (8 : ℝ) / 3 < Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have ha1 : (0 : ℝ) ≤ (a : ℝ) - 1 := by
    have : (2 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  have : (8 : ℝ) * ((a : ℝ) - 1) < 3 * M := by nlinarith
  have hc : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [← hc] at this
  exact_mod_cast this

end Erdos287.PostQSigma
