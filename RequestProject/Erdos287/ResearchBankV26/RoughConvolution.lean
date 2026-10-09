import Mathlib

/-!
# Erdős #287 — Research Bank V26 §4.1: rough convolution identities

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For `z ∈ ℕ` put

    R_z(n) = 1_{P⁻(n) ≥ z}   (every prime factor of n is ≥ z; R_z(1) = 1),
    H_z(d) = 1_{P⁺(d) < z}   (every prime factor of d is < z; H_z(1) = 1),

both zero at `0`.  `H_z` is the indicator of ALL `z`-smooth integers, prime powers included — it is
NOT silently replaced by its squarefree part.

**LEAN BANK.**

* `primeIndicator_isMultiplicative` — `n ↦ 1_{n ≠ 0 ∧ ∀ p ∣ n, P p}` is multiplicative;
* **`rough_mu_identity`** — `μ · R_z = μ ⋆ H_z` (as arithmetic functions);
* **`rough_one_identity`** — `R_z = 1 ⋆ (μ · H_z)`;
* `rough_mu_identity_apply`, `rough_one_identity_apply` — the pointwise divisor-sum forms
  `μ(n) R_z(n) = Σ_{d ∣ n} μ(d) H_z(n/d)` and `R_z(n) = Σ_{d ∣ n} μ(d) H_z(d)`.
-/

namespace Erdos287
namespace ResearchBankV26
namespace RoughConvolution

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- The indicator `1_{n ≠ 0 ∧ ∀ p ∈ primeFactors n, P p}`. -/
noncomputable def primeIndicator (P : ℕ → Prop) [DecidablePred P] : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, P p then 1 else 0, by simp⟩

theorem primeIndicator_apply (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    primeIndicator P n = if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, P p then 1 else 0 := rfl

/-- `R_z = 1_{P⁻(n) ≥ z}`. -/
noncomputable def R (z : ℕ) : ArithmeticFunction ℤ := primeIndicator (fun p => z ≤ p)

/-- `H_z = 1_{P⁺(d) < z}` (all smooth integers, prime powers included). -/
noncomputable def H (z : ℕ) : ArithmeticFunction ℤ := primeIndicator (fun p => p < z)

theorem primeIndicator_isMultiplicative (P : ℕ → Prop) [DecidablePred P] :
    (primeIndicator P).IsMultiplicative := by
  refine ⟨by simp [primeIndicator_apply], fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [primeIndicator_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [primeIndicator_apply]
  have key : (∀ p ∈ (m * n).primeFactors, P p) ↔
      (∀ p ∈ m.primeFactors, P p) ∧ (∀ p ∈ n.primeFactors, P p) := by
    rw [Nat.primeFactors_mul hm hn]
    simp only [Finset.mem_union, or_imp, forall_and]
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
  simp only [primeIndicator_apply, key]
  rw [ite_zero_mul_ite_zero, one_mul]
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem primeIndicator_prime_pow (P : ℕ → Prop) [DecidablePred P] {p : ℕ} (hp : p.Prime)
    (i : ℕ) : primeIndicator P (p ^ i) = if i = 0 then 1 else if P p then 1 else 0 := by
  rcases eq_or_ne i 0 with rfl | hi
  · simp [primeIndicator_apply]
  rw [primeIndicator_apply, Nat.primeFactors_prime_pow hi hp, if_neg hi]
  simp [hp.ne_zero]

/-- Sum over the divisor antidiagonal of a prime power. -/
theorem sum_antidiag_prime_pow (f g : ArithmeticFunction ℤ) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (f * g) (p ^ i) = ∑ j ∈ Finset.range (i + 1), f (p ^ j) * g (p ^ (i - j)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b), Nat.divisors_prime_pow hp,
    Finset.sum_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (by simpa [Nat.lt_succ_iff] using hj) hp.pos]

theorem moebius_prime_pow' {p : ℕ} (hp : p.Prime) (j : ℕ) :
    μ (p ^ j) = if j = 0 then 1 else if j = 1 then -1 else 0 := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · rw [moebius_apply_prime_pow hp hj, if_neg hj]

/-- **`μ · R_z = μ ⋆ H_z`** (LEAN BANK). -/
theorem rough_mu_identity (z : ℕ) : (μ : ArithmeticFunction ℤ).pmul (R z) = μ * H z := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_moebius.pmul (primeIndicator_isMultiplicative _)) _
    (isMultiplicative_moebius.mul (primeIndicator_isMultiplicative _))).2 fun p i hp => ?_
  rw [pmul_apply, sum_antidiag_prime_pow _ _ hp]
  rcases i with _ | i
  · simp [primeIndicator_apply]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∀ j ∈ Finset.range i, μ (p ^ (j + 1 + 1)) * primeIndicator (fun p => p < z)
      (p ^ (i + 1 - (j + 1 + 1))) = 0 := fun j _ => by
    rw [moebius_prime_pow' hp]; simp
  rw [Finset.sum_eq_zero hz, moebius_prime_pow' hp, moebius_prime_pow' hp, moebius_prime_pow' hp,
    primeIndicator_prime_pow _ hp, primeIndicator_prime_pow _ hp, primeIndicator_prime_pow _ hp]
  rcases i with _ | i <;> by_cases hzp : p < z <;> simp [hzp, not_lt.1]

/-- **`R_z = 1 ⋆ (μ · H_z)`** (LEAN BANK). -/
theorem rough_one_identity (z : ℕ) : R z = (ζ : ArithmeticFunction ℤ) * (μ : ArithmeticFunction ℤ).pmul (H z) := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (primeIndicator_isMultiplicative _) _
    (isMultiplicative_zeta.natCast.mul
      (isMultiplicative_moebius.pmul (primeIndicator_isMultiplicative _)))).2 fun p i hp => ?_
  rw [coe_zeta_mul_apply, Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, pmul_apply]
  rcases i with _ | i
  · simp [primeIndicator_apply]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∀ j ∈ Finset.range i, μ (p ^ (j + 1 + 1)) * primeIndicator (fun p => p < z)
      (p ^ (j + 1 + 1)) = 0 := fun j _ => by
    rw [moebius_prime_pow' hp]; simp
  rw [Finset.sum_eq_zero hz, moebius_prime_pow' hp, moebius_prime_pow' hp,
    primeIndicator_prime_pow _ hp, primeIndicator_prime_pow _ hp, primeIndicator_prime_pow _ hp]
  by_cases hzp : p < z <;> simp [hzp, not_lt.1]

/-- Pointwise form: `μ(n) R_z(n) = Σ_{d ∣ n} μ(d) H_z(n/d)`. -/
theorem rough_mu_identity_apply (z n : ℕ) :
    μ n * R z n = ∑ d ∈ n.divisors, μ d * H z (n / d) := by
  have := congrArg (fun F : ArithmeticFunction ℤ => F n) (rough_mu_identity z)
  simp only [pmul_apply, mul_apply] at this
  rw [this, Nat.sum_divisorsAntidiagonal (fun a b => μ a * H z b)]

/-- Pointwise form: `R_z(n) = Σ_{d ∣ n} μ(d) H_z(d)`. -/
theorem rough_one_identity_apply (z n : ℕ) :
    R z n = ∑ d ∈ n.divisors, μ d * H z d := by
  have := congrArg (fun F : ArithmeticFunction ℤ => F n) (rough_one_identity z)
  simp only [coe_zeta_mul_apply, pmul_apply] at this
  exact this

end RoughConvolution
end ResearchBankV26
end Erdos287
