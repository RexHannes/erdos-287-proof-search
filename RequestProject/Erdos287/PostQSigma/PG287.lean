import RequestProject.Erdos287.PostQSigma.ProperModulusGram
import RequestProject.Erdos287.PostQSigma.PathCount

/-!
# Erdős #287 — post-`Q_Σ` bank, §37–38 (V64): PG-287 (DEFINED, NOT PROVED) and its closure

**`PG287` is PROVISIONAL / OPEN.**  It is *defined* here as a proposition; it is **not**
proved, assumed globally, or instantiated anywhere in the repository.

`PG287 a M` : there is a rational weight vector `λ` on the proper moduli `Lset W` with
`∑_q λ_q = 1` and

  `λᵀ G λ ≤ M^100 · W^{-12/25} · P`,

stated in the exact integer-safe form `(λᵀGλ)^25 · W^12 ≤ (M^100 · P)^25` (both sides are
nonnegative, so this is equivalent; no negative rational powers are used).

The external analytic input `PsiLowerBound` (`ψ(M) ≥ 0.9 M` for `M ≥ 41`, in the form
`exp(9M/10) ≤ lcm(1,…,M)`) is **EXTERNAL MATHEMATICAL INPUT NOT FORMALISED LOCALLY**; it is a
named proposition used only as an explicit hypothesis.

Proved here:

* `count_zero_of_PG287` — `PG287` + `(M^100 P)^25 < W^12` ⇒ `N_T < 1` ⇒ `N_T = 0`;
* `pow_le_exp_of_large` — `M^2500 ≤ exp(3M/10)` for `M ≥ 2^1500`;
* `capacity_closure` — `P < exp(21M/50)`, `exp(9M/10) ≤ W`, `M ≥ 2^1500`
  ⇒ `(M^100 · P)^25 < W^12` (i.e. `M^100 W^{-12/25} P < 1`);
* `PG287_implies_no_tail_source` — the exact infinite-tail implication for the raw source.
-/

open scoped BigOperators

namespace Erdos287.PostQSigma

open Erdos287.ExactSource

/-- **PG-287 (OPEN; definition only).**  The proper-modulus Gram capacity proposition. -/
def PG287 (a M : ℕ) : Prop :=
  ∃ lam : ℕ → ℚ, ∑ q ∈ Lset (W a M ∅), lam q = 1 ∧
    (physQuad a M lam) ^ 25 * (W a M ∅ : ℚ) ^ 12 ≤ ((M : ℚ) ^ 100 * Ptot a M) ^ 25

/-- **External input (not formalised locally)**: `ψ(M) ≥ 0.9 M` for `M ≥ 41`, i.e.
`exp(9M/10) ≤ lcm(1,…,M)`.  Used only as an explicit hypothesis. -/
def PsiLowerBound : Prop :=
  ∀ M : ℕ, 41 ≤ M → Real.exp (9 * M / 10) ≤ (((Finset.Icc 1 M).lcm id : ℕ) : ℝ)

/-- `PG287` + capacity arithmetic ⇒ `N_T = 0`. -/
theorem count_zero_of_PG287 {a M : ℕ} (h : PG287 a M)
    (hcap : ((M : ℚ) ^ 100 * Ptot a M) ^ 25 < (W a M ∅ : ℚ) ^ 12) : NT a M = 0 := by
  obtain ⟨lam, hsum, hle⟩ := h
  have hmaj := proper_modulus_majorant (a := a) (M := M) lam hsum
  have hQ0 := proper_modulus_gram_psd (a := a) (M := M) lam
  set Q := physQuad a M lam
  have hWpos : (0 : ℚ) < (W a M ∅ : ℚ) ^ 12 := by
    have : (0 : ℚ) ≤ (W a M ∅ : ℚ) := by positivity
    rcases this.lt_or_eq with h' | h'
    · positivity
    · rw [← h'] at hcap; simp at hcap
      exact absurd hcap (not_lt.2 (by positivity))
  have hQ25 : Q ^ 25 < 1 := by
    by_contra hc; push_neg at hc
    have : (W a M ∅ : ℚ) ^ 12 ≤ Q ^ 25 * (W a M ∅ : ℚ) ^ 12 := by nlinarith
    linarith
  have hQ1 : Q < 1 := by
    by_contra hc; push_neg at hc
    have := one_le_pow₀ (n := 25) hc
    linarith
  have : (NT a M : ℚ) < 1 := lt_of_le_of_lt hmaj hQ1
  have : NT a M < 1 := by exact_mod_cast this
  omega

/-- `M^2500 ≤ exp(3M/10)` for `M ≥ 2^1500` (via `log x ≤ x - 1` at `x = √M`). -/
theorem pow_le_exp_of_large {M : ℝ} (hM : (2 : ℝ) ^ 1500 ≤ M) :
    M ^ 2500 ≤ Real.exp (3 * M / 10) := by
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  set s := Real.sqrt M with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hM0
  have hss : s ^ 2 = M := Real.sq_sqrt hM0.le
  have h30 : (2 : ℝ) ^ 30 ≤ 2 ^ 1500 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hbig : (10 : ℝ) ^ 9 ≤ M := le_trans (le_trans (by norm_num) h30) hM
  clear h30 hM
  have hs_big : (20000 : ℝ) ≤ s := by
    rw [hs, Real.le_sqrt (by norm_num) hM0.le]; linarith
  have hlog : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  have h1 : M ^ 2500 = Real.exp (5000 * Real.log s) := by
    rw [← hss, ← pow_mul, ← Real.exp_log (pow_pos hs0 _), Real.log_pow]; norm_num
  rw [h1, Real.exp_le_exp, ← hss]
  nlinarith [mul_le_mul_of_nonneg_left hs_big hs0.le]

/-- **Capacity closure arithmetic**: `M^100 · W^{-12/25} · P < 1` in the integer-safe form. -/
theorem capacity_closure {M P W : ℕ} (hM : 2 ^ 1500 ≤ M) (hP : (P : ℝ) < Real.exp (21 * M / 50))
    (hW : Real.exp (9 * M / 10) ≤ (W : ℝ)) :
    ((M : ℚ) ^ 100 * P) ^ 25 < (W : ℚ) ^ 12 := by
  have hMr : (2 : ℝ) ^ 1500 ≤ (M : ℝ) := by exact_mod_cast hM
  have h1 := pow_le_exp_of_large hMr
  have hP0 : (0 : ℝ) ≤ P := by positivity
  have hM0 : (0 : ℝ) < (M : ℝ) ^ 2500 := by
    have : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hMr
    positivity
  have h2 : (P : ℝ) ^ 25 < Real.exp (21 * M / 50) ^ 25 := pow_lt_pow_left₀ hP hP0 (by norm_num)
  have h3 : Real.exp (9 * M / 10) ^ 12 ≤ (W : ℝ) ^ 12 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hW 12
  have key : ((M : ℝ) ^ 100 * P) ^ 25 < (W : ℝ) ^ 12 := by
    rw [mul_pow, ← pow_mul]
    calc (M : ℝ) ^ (100 * 25) * (P : ℝ) ^ 25 < (M : ℝ) ^ 2500 * Real.exp (21 * M / 50) ^ 25 := by
          norm_num; exact mul_lt_mul_of_pos_left h2 hM0
      _ ≤ Real.exp (3 * M / 10) * Real.exp (21 * M / 50) ^ 25 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = Real.exp (9 * M / 10) ^ 12 := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
      _ ≤ (W : ℝ) ^ 12 := h3
  exact_mod_cast key

/-- **PG-287 ⇒ no tail source** (exact infinite-tail implication, conditional on the explicit
external input `PsiLowerBound` and on the *open* proposition `PG287 a M`). -/
theorem PG287_implies_no_tail_source (hpsi : PsiLowerBound) {a M : ℕ} (hM : 2 ^ 1500 ≤ M)
    (h16 : 16 * M < 121 * a) (h2a : 2 * a ≤ M) (hPG : PG287 a M) :
    ∀ E, ¬ SourceSol a M ∅ E := by
  have h12 : ∀ k, 12 ≤ k → (2 : ℕ) ^ 12 ≤ 2 ^ k := fun k hk => Nat.pow_le_pow_right (by norm_num) hk
  have hM3000 : 3000 ≤ M :=
    le_trans (show (3000 : ℕ) ≤ 2 ^ 12 by norm_num) (le_trans (h12 1500 (by norm_num)) hM)
  clear h12
  have ha0 : 0 < a := by omega
  have haM : a < M := by omega
  have hP := Ptot_lt_exp haM h16 hM3000
  have hWeq := W_raw_eq_lcm_one ha0 (by omega : 2 * a ≤ M + 2)
  have hW : Real.exp (9 * M / 10) ≤ (W a M ∅ : ℝ) := by
    rw [hWeq]; exact hpsi M (by omega)
  have hcap := capacity_closure hM hP hW
  exact NT_eq_zero_iff.1 (count_zero_of_PG287 hPG hcap)

end Erdos287.PostQSigma
