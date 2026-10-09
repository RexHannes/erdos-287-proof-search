import RequestProject.Erdos287.Effective.LcmBound

/-!
# Erdős #287 — structural audit of the Lean size-biased measure and hinge statistic

**ERDŐS #287 REMAINS OPEN.**  V103's literal text is not in the repository, so the comparison
is recorded as kernel-proved structural facts about the Lean definitions, one per audited
feature:

* **multiplicity** — `sbMeasure_prime_pow`: `μ_{q^k}(q) = 1`, i.e. `v_q(n)` is counted with
  multiplicity (not `1_{q ∣ n}`);
* **support** — `sbMeasure_eq_zero_of_not_dvd`: `μ_n(q) = 0` unless `q ∣ n`;
* **normalization** — `sbMeasure_sum` (existing): `∑_{q ∣ n} μ_n(q) = 1` for `n ≥ 2`; hence
  `hingeT_le_two_mul_card`: `T_M ≤ 2 · #{p prime : M/2 < p ≤ M}` (each of `p ± 1` has mass `≤ 1`);
* **moving endpoint** — `Hstar_mono`: `H_*(M)` is monotone in `M`, so the cofactor threshold
  `⌊(H_*(M) - 1)/2⌋` of `T_M` moves (weakly) upward with `M`; `floor_log_le_Hstar` gives its
  logarithmic growth.
-/

open Finset

set_option autoImplicit false

namespace Erdos287.Effective

/-- **Support**: `μ_n(q) = 0` unless `q ∣ n`. -/
theorem sbMeasure_eq_zero_of_not_dvd {n q : ℕ} (h : ¬ q ∣ n) : sbMeasure n q = 0 := by
  unfold sbMeasure
  rw [Nat.factorization_eq_zero_of_not_dvd h]
  simp

/-- **Multiplicity**: `μ_{q^k}(q) = 1` for a prime `q` and `k ≥ 1`. -/
theorem sbMeasure_prime_pow {q k : ℕ} (hq : q.Prime) (hk : 1 ≤ k) : sbMeasure (q ^ k) q = 1 := by
  unfold sbMeasure
  rw [Nat.Prime.factorization_pow hq, Finsupp.single_eq_same, Nat.cast_pow, Real.log_pow]
  have : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  field_simp

/-- **Moving endpoint**: `H_*` is monotone. -/
theorem Hstar_mono {M M' : ℕ} (h : M ≤ M') : Hstar M ≤ Hstar M' :=
  Nat.findGreatest_mono (fun _ hx => lt_of_lt_of_le hx h) h

lemma inner_mass_le_one (n : ℕ) (t : ℕ) :
    ∑ q ∈ n.primeFactors, (if n / q ≤ t then sbMeasure n q else 0) ≤ 1 := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  calc ∑ q ∈ n.primeFactors, (if n / q ≤ t then sbMeasure n q else 0)
      ≤ ∑ q ∈ n.primeFactors, sbMeasure n q := by
        refine sum_le_sum (fun q _ => ?_)
        split_ifs
        · exact le_rfl
        · exact sbMeasure_nonneg n q
    _ = 1 := sbMeasure_sum hn

/-- **Normalization of `T_M`**: `T_M ≤ 2 · #{p prime : M/2 < p ≤ M}`. -/
theorem hingeT_le_two_mul_card (M : ℕ) : hingeT M ≤ 2 * (hingePrimes M).card := by
  unfold hingeT
  have : (2 : ℝ) * (hingePrimes M).card = ∑ _p ∈ hingePrimes M, (2 : ℝ) := by
    rw [sum_const, nsmul_eq_mul, mul_comm]
  rw [this]
  refine sum_le_sum (fun p _ => ?_)
  calc ∑ n ∈ ({p - 1, p + 1} : Finset ℕ), ∑ q ∈ n.primeFactors,
        (if n / q ≤ (Hstar M - 1) / 2 then sbMeasure n q else 0)
      ≤ ∑ _n ∈ ({p - 1, p + 1} : Finset ℕ), (1 : ℝ) :=
        sum_le_sum (fun n _ => inner_mass_le_one n _)
    _ ≤ 2 := by
        rw [sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast card_le_two

end Erdos287.Effective
