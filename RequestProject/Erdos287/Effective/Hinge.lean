import RequestProject.Erdos287.Effective.Finisher

/-!
# Erdős #287 — V103 effectivity: height, hinge statistic, conditional global implication

**ERDŐS #287 REMAINS OPEN.  No analytic hinge estimate is assumed or claimed here.**

* `Hstar_spec`, `le_Hstar` — `H_*(M)` is the maximal uniform height.
* `onset_nat`, `onset_exp` — **arithmetic onset**: `M ≥ e^{12}` (indeed `M ≥ 73811`) gives
  `H_*(M) ≥ 10`, so the one-prime finisher admits every cofactor `a ≤ 4`.
* `log_height_of_lcm_bound` — **conservative logarithmic height**: under the Chebyshev-type
  input `L_h ≤ 3^h` (stated as an explicit hypothesis `LcmBound3`; it is a classical theorem
  but not available in Mathlib), `9^h < M ⇒ h ≤ H_*(M)`, i.e. `H_*(M) ≥ ⌈log M / log 9⌉ - 1`;
  `lcmBound3_le_40` verifies the input for all `h ≤ 40` by kernel computation.
* `sbMeasure n q = v_q(n) log q / log n` — the **size-biased prime-factor measure** of `n`;
  `sbMeasure_nonneg`, `sbMeasure_sum` (a probability measure on the primes of `n ≥ 2`).
* `hingeT M` — the hinge statistic: total size-biased mass of prime factors `q` of `p ± 1`
  (`p` prime, `M/2 < p ≤ M`) whose cofactor `(p±1)/q` is at most `⌊(H_*(M)-1)/2⌋`.
* `not_ce_of_hingeT_pos` — `T_M > 0 ⇒ ¬ Counterexample287 M` (via `one_prime_finisher`).
* `no_ce_of_finite_and_hinge` — **conditional** global implication: a separately certified
  finite exclusion below `M₀` plus an explicit uniform lower bound `T_M ≥ c > 0` for `M ≥ M₀`
  exclude every gap-`≤ 2` counterexample.  Both inputs are hypotheses.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Effective

/-! ### The maximal uniform height -/

theorem Hstar_spec {M : ℕ} (hM : 0 < M) : Hstar M * Bh (Hstar M) < M :=
  Nat.findGreatest_spec (P := fun h => h * Bh h < M) (m := 0) (Nat.zero_le _) (by simpa using hM)

theorem le_Hstar {M h : ℕ} (hh : h * Bh h < M) : h ≤ Hstar M := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · exact Nat.zero_le _
  refine Nat.le_findGreatest ?_ hh
  have := one_le_Bh hpos
  nlinarith

/-- **Arithmetic onset** (natural form): `M ≥ 73811 ⇒ H_*(M) ≥ 10`. -/
theorem onset_nat {M : ℕ} (hM : 73811 ≤ M) : 10 ≤ Hstar M := by
  refine le_Hstar ?_
  rw [show Bh 10 = 7381 by decide]
  omega

/-- **Arithmetic onset**: `M ≥ e^{12} ⇒ H_*(M) ≥ 10`. -/
theorem onset_exp {M : ℕ} (hM : Real.exp 12 ≤ M) : 10 ≤ Hstar M := by
  refine onset_nat ?_
  have he : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h12 : Real.exp 12 = Real.exp 1 ^ 12 := by
    rw [← Real.exp_nat_mul]; norm_num
  have : (73811 : ℝ) < Real.exp 12 := by
    rw [h12]
    calc (73811 : ℝ) < 2.7 ^ 12 := by norm_num
      _ < Real.exp 1 ^ 12 := pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  have : (73811 : ℝ) < M := lt_of_lt_of_le this hM
  exact_mod_cast this.le

/-- The Chebyshev-type input `lcm(1,…,h) ≤ 3^h` (classical; not in Mathlib). -/
def LcmBound3 : Prop := ∀ h, Lh h ≤ 3 ^ h

/-- The input holds for `h ≤ 40` (kernel computation). -/
theorem lcmBound3_le_40 : ∀ h ≤ 40, Lh h ≤ 3 ^ h := by decide

lemma Bh_le (h : ℕ) : Bh h ≤ h * Lh h := by
  unfold Bh
  calc ∑ j ∈ Icc 1 h, Lh h / j ≤ ∑ _j ∈ Icc 1 h, Lh h := sum_le_sum (fun _ _ => Nat.div_le_self _ _)
    _ = h * Lh h := by rw [sum_const, Nat.card_Icc, smul_eq_mul]; congr 1

lemma sq_le_three_pow (h : ℕ) : h ^ 2 ≤ 3 ^ h := by
  induction h with
  | zero => simp
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> norm_num
    · rw [pow_succ 3, show (n+1)^2 = n^2+2*n+1 by ring]
      nlinarith [ih]

/-- **Conservative logarithmic height** (conditional on `LcmBound3`): `9^h < M ⇒ h ≤ H_*(M)`. -/
theorem log_height_of_lcm_bound (hL : LcmBound3) {M h : ℕ} (hM : 9 ^ h < M) : h ≤ Hstar M := by
  refine le_Hstar (lt_of_le_of_lt ?_ hM)
  calc h * Bh h ≤ h * (h * Lh h) := Nat.mul_le_mul_left _ (Bh_le h)
    _ = h ^ 2 * Lh h := by ring
    _ ≤ 3 ^ h * 3 ^ h := Nat.mul_le_mul (sq_le_three_pow h) (hL h)
    _ = 9 ^ h := by rw [← mul_pow]; norm_num

/-! ### The size-biased prime-factor measure -/

/-- `μ_n(q) = v_q(n) log q / log n`. -/
noncomputable def sbMeasure (n q : ℕ) : ℝ := (n.factorization q : ℝ) * Real.log q / Real.log n

theorem sbMeasure_nonneg (n q : ℕ) : 0 ≤ sbMeasure n q := by
  unfold sbMeasure
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg q))
    (Real.log_natCast_nonneg n)

/-- `μ_n` is a probability measure on the prime factors of `n ≥ 2`. -/
theorem sbMeasure_sum {n : ℕ} (hn : 2 ≤ n) : ∑ q ∈ n.primeFactors, sbMeasure n q = 1 := by
  have hn0 : n ≠ 0 := by omega
  have hlog : Real.log n = ∑ q ∈ n.primeFactors, (n.factorization q : ℝ) * Real.log q := by
    have h := Nat.factorization_prod_pow_eq_self hn0
    rw [Finsupp.prod, Nat.support_factorization] at h
    conv_lhs => rw [← h]
    push_cast
    rw [Real.log_prod]
    · refine sum_congr rfl (fun q _ => ?_)
      rw [Real.log_pow]
    · intro q hq
      exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).ne_zero)
  have hpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  unfold sbMeasure
  rw [← sum_div, ← hlog, div_self hpos.ne']

/-! ### The hinge statistic -/

/-- Primes `p` with `M/2 < p ≤ M`. -/
def hingePrimes (M : ℕ) : Finset ℕ := (Icc 1 M).filter (fun p => p.Prime ∧ M < 2 * p)

/-- **The hinge statistic** `T_M`. -/
noncomputable def hingeT (M : ℕ) : ℝ :=
  ∑ p ∈ hingePrimes M, ∑ n ∈ ({p - 1, p + 1} : Finset ℕ), ∑ q ∈ n.primeFactors,
    if n / q ≤ (Hstar M - 1) / 2 then sbMeasure n q else 0

/-- **`T_M > 0 ⇒ ¬ Counterexample287 M`.** -/
theorem not_ce_of_hingeT_pos {M : ℕ} (hT : 0 < hingeT M) : ¬ Counterexample287 M := by
  unfold hingeT at hT
  obtain ⟨p, hp, hT1⟩ := exists_pos_of_sum_pos hT
  obtain ⟨n, hn, hT2⟩ := exists_pos_of_sum_pos hT1
  obtain ⟨q, hq, hT3⟩ := exists_pos_of_sum_pos hT2
  have hcof : n / q ≤ (Hstar M - 1) / 2 := by
    by_contra hc; rw [if_neg hc] at hT3; exact lt_irrefl _ hT3
  obtain ⟨-, hpP, hp2⟩ := (mem_filter.1 hp)
  have hpM : p ≤ M := (mem_Icc.1 (mem_filter.1 hp).1).2
  have hqP := Nat.prime_of_mem_primeFactors hq
  have hqd := Nat.dvd_of_mem_primeFactors hq
  have hM0 : 0 < M := lt_of_lt_of_le hpP.pos hpM
  have hnaq : n = n / q * q := (Nat.div_mul_cancel hqd).symm
  refine one_prime_finisher M (Hstar M) p q (n / q) (Hstar_spec hM0) hpP hp2 hpM hqP ?_ hcof
  rcases mem_insert.1 hn with rfl | hn'
  · exact Or.inr hnaq
  · rw [mem_singleton] at hn'; subst hn'; exact Or.inl hnaq
  where
    exists_pos_of_sum_pos {ι : Type} {s : Finset ι} {f : ι → ℝ} (h : 0 < ∑ i ∈ s, f i) :
        ∃ i ∈ s, 0 < f i := by
      by_contra hc
      push_neg at hc
      exact absurd (sum_nonpos hc) (not_le.2 h)

/-! ### Conditional global implication -/

/-- A separately certified finite exclusion below `M₀` (hypothesis). -/
def FiniteExclusion (M₀ : ℕ) : Prop := ∀ M, M < M₀ → ¬ Counterexample287 M

/-- An explicit uniform hinge lower bound `T_M ≥ c > 0` for `M ≥ M₀` (hypothesis; **not**
established here). -/
def UniformHingeBound (M₀ : ℕ) (c : ℝ) : Prop := 0 < c ∧ ∀ M, M₀ ≤ M → c ≤ hingeT M

/-- **Conditional global implication.** -/
theorem no_ce_of_finite_and_hinge {M₀ : ℕ} {c : ℝ} (hF : FiniteExclusion M₀)
    (hH : UniformHingeBound M₀ c) : ∀ M, ¬ Counterexample287 M := by
  intro M
  rcases Nat.lt_or_ge M M₀ with h | h
  · exact hF M h
  · exact not_ce_of_hingeT_pos (lt_of_lt_of_le hH.1 (hH.2 M h))

end Erdos287.Effective
