import Mathlib
import RequestProject.TrustedBank.Gate1B.CenteredRho

/-!
# Gate 1B — clean squarefree Möbius collapse

For `q = d·p` with `p` prime, `d` squarefree and `gcd(d,p) = 1` we prove `μ d = -μ q`,
and then the **product-separable** collapse

```
∑_{d·p = q, p prime}  μ(d) · logWeight(p) · DWeight(d) · PWeight(p)
      = -μ(q) · LambdaSharp(q),
```

where `LambdaSharp` is the *finite* localized log-prime sum restricted to a `P`-box and a
`D`-box.

The theorem is stated **only** for product-separable weights.  A nonseparable
two-variable weight `W(d,p)` is handled in `SeparableWeights.lean` through an explicit
decomposition record, never by extending this theorem.

Hostile tests at the end show the collapse genuinely fails for a non-squarefree `q`
(the repeated-prime sector `q = p²`).
-/

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace TrustedBank
namespace Gate1B

/-- **μ d = -μ q** for `q = d·p`, `p` prime, `d` squarefree, `gcd(d,p) = 1`. -/
theorem moebius_of_prime_times_squarefree {d p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime d p) :
    (μ d : ℤ) = -(μ (d * p) : ℤ) := by
  have hmul : (μ (d * p) : ℤ) = (μ d : ℤ) * (μ p : ℤ) :=
    isMultiplicative_moebius.map_mul_of_coprime hcop
  rw [hmul, ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- For a squarefree `q` and a prime `p ∣ q`, the cofactor `q/p` is coprime to `p`. -/
theorem coprime_div_prime {q p : ℕ} (hq : Squarefree q) (hp : p.Prime) (hpq : p ∣ q) :
    Nat.Coprime (q / p) p := by
  rcases hpq with ⟨c, rfl⟩
  have hc : p * c / p = c := Nat.mul_div_cancel_left _ hp.pos
  rw [hc]
  have hnd : ¬ p ∣ c := by
    rintro ⟨k, rfl⟩
    exact hp.not_isUnit (hq p ⟨k, by ring⟩)
  exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm

/-- **Cofactor Möbius rule.**  For squarefree `q` and prime `p ∣ q`, `μ (q/p) = -μ q`. -/
theorem moebius_div_prime {q p : ℕ} (hq : Squarefree q) (hp : p.Prime) (hpq : p ∣ q) :
    (μ (q / p) : ℤ) = -(μ q : ℤ) := by
  have hcop : Nat.Coprime (q / p) p := coprime_div_prime hq hp hpq
  have hqe : q / p * p = q := Nat.div_mul_cancel hpq
  have := moebius_of_prime_times_squarefree (d := q / p) hp hcop
  rwa [hqe] at this

/-- The finite localized log-prime sum, restricted to a `P`-box and a `D`-box.
Only prime divisors `p` of `q` with `p ∈ Pbox` and `q/p ∈ Dbox` contribute. -/
def LambdaSharp (Pbox Dbox : Finset ℕ) (logW PW DW : ℕ → ℚ) (q : ℕ) : ℚ :=
  ∑ p ∈ q.primeFactors.filter (fun p => p ∈ Pbox ∧ q / p ∈ Dbox),
    logW p * PW p * DW (q / p)

/-- **Clean squarefree Möbius collapse (product-separable weights only).** -/
theorem mmd_clean_collapse {q : ℕ} (hq : Squarefree q)
    (Pbox Dbox : Finset ℕ) (logW PW DW : ℕ → ℚ) :
    ∑ p ∈ q.primeFactors.filter (fun p => p ∈ Pbox ∧ q / p ∈ Dbox),
        ((μ (q / p) : ℤ) : ℚ) * logW p * DW (q / p) * PW p
      = -((μ q : ℤ) : ℚ) * LambdaSharp Pbox Dbox logW PW DW q := by
  rw [LambdaSharp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := Finset.mem_filter.mp hp
  have hprime : p.Prime := (Nat.mem_primeFactors.mp hp'.1).1
  have hpq : p ∣ q := (Nat.mem_primeFactors.mp hp'.1).2.1
  have h := moebius_div_prime hq hprime hpq
  rw [h]
  push_cast
  ring

/-! ## Hostile tests: the repeated-prime sector must not enter -/

/-- `μ (p²) = 0` for every prime `p`: the repeated-prime sector is annihilated, and the
cofactor rule `μ(q/p) = -μ q` cannot hold there. -/
theorem moebius_prime_sq_eq_zero {p : ℕ} (hp : p.Prime) : (μ (p ^ 2) : ℤ) = 0 := by
  refine ArithmeticFunction.moebius_eq_zero_of_not_squarefree ?_
  intro hsq
  exact hp.not_isUnit (hsq p (by rw [sq]))

/-- **Squarefreeness is required.**  With `q = 4 = 2²` and `p = 2` we have `μ(q/p) = -1`
but `-μ q = 0`, so the cofactor rule (hence the clean collapse) fails outside the
squarefree sector. -/
theorem moebius_div_prime_fails_at_prime_square :
    ∃ q p : ℕ, p.Prime ∧ p ∣ q ∧ ¬ Squarefree q ∧ ((μ (q / p) : ℤ) ≠ -(μ q : ℤ)) := by
  refine ⟨4, 2, Nat.prime_two, by decide, by decide +kernel, ?_⟩
  have h2 : (μ 2 : ℤ) = -1 := ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h4 : (μ 4 : ℤ) = 0 := by
    simpa using moebius_prime_sq_eq_zero Nat.prime_two
  norm_num [show (4 : ℕ) / 2 = 2 from rfl, h2, h4]

/-- Sanity test on a genuine squarefree cell `q = 6`. -/
theorem moebius_div_prime_test_six :
    ((μ (6 / 2) : ℤ)) = -((μ 6 : ℤ)) ∧ ((μ (6 / 3) : ℤ)) = -((μ 6 : ℤ)) :=
  ⟨moebius_div_prime (by decide +kernel) Nat.prime_two (by decide),
   moebius_div_prime (by decide +kernel) Nat.prime_three (by decide)⟩

end Gate1B
end TrustedBank
