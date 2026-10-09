import Mathlib
import RequestProject.Erdos287.BsrcWeights

/-!
# Erdős #287 effectivity — the λ(b) finite algebra (§25)

```
LAMBDA FINITE ALGEBRA : KERNEL-PROVED
LAMBDA POSITIVITY     : KERNEL-PROVED
LOCAL EULER ALGEBRA   : KERNEL-PROVED
H_lambda(0) < 8/3     : CONDITIONAL (finite part exact, tail is a supplied hypothesis)
```

For odd squarefree `b` the λ-weight of the long-fibre chart is

    λ(b) = ∏_{p ∣ b} (p−1)/(p−2)².

Everything here is a **finite** product over `Nat.primeFactors`; no infinite Euler product
is asserted anywhere.  The exact local algebra linking λ to the banked source weights is

    λ(b) = B0(b) · β(b)      (`b` odd squarefree),

so the λ-chart is the `β`-twist of the physical `B0`-chart, factor by factor.

The value `H_λ(0)` of the source is *not* defined in this package: it is an infinite Euler
product whose convergence is not kernel-owned.  §25.4 therefore separates the three layers
required by the brief: a finite exact product theorem, an explicit analytic-tail hypothesis
carried as data, and the conditional combination.  Nothing here proves `H_λ(0) < 8/3`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §25.1  Definition -/

/-- The local λ-factor at an odd prime: `(p−1)/(p−2)²`. -/
def lambdaLocal (p : ℕ) : ℚ := ((p : ℚ) - 1) / ((p : ℚ) - 2) ^ 2

/-- `λ(b) = ∏_{p ∣ b, p > 2} (p−1)/(p−2)²`, a finite product over the odd prime factors. -/
def lambdaW (b : ℕ) : ℚ := ∏ p ∈ oddPrimeFactors b, lambdaLocal p

@[simp] theorem lambdaW_one : lambdaW 1 = 1 := by simp [lambdaW, oddPrimeFactors]

@[simp] theorem lambdaW_zero : lambdaW 0 = 1 := by simp [lambdaW, oddPrimeFactors]

/-- λ at an odd prime. -/
theorem lambdaW_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    lambdaW p = ((p : ℚ) - 1) / ((p : ℚ) - 2) ^ 2 := by
  rw [lambdaW, oddPrimeFactors, hp.primeFactors,
    Finset.erase_eq_of_notMem (by simpa using Ne.symm h2), Finset.prod_singleton, lambdaLocal]

/-- λ ignores the prime `2`. -/
@[simp] theorem lambdaW_two_pow (k : ℕ) : lambdaW (2 ^ k) = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [lambdaW, oddPrimeFactors, Nat.primeFactors_prime_pow hk.ne' Nat.prime_two]
    simp

/-! ## §25.2  Multiplicativity and positivity -/

/-- **`lambdaW_mul`.**  `KERNEL-PROVED`.  λ is multiplicative on coprime nonzero
arguments. -/
theorem lambdaW_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b) :
    lambdaW (a * b) = lambdaW a * lambdaW b := by
  rw [lambdaW, lambdaW, lambdaW, oddPrimeFactors_mul ha hb, Finset.prod_union]
  refine Finset.disjoint_left.2 fun p hpa hpb => ?_
  exact (Finset.disjoint_left.1 hab.disjoint_primeFactors
    (mem_oddPrimeFactors.1 hpa).2) (mem_oddPrimeFactors.1 hpb).2

/-- The local λ-factor at an odd prime is positive. -/
theorem lambdaLocal_pos {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : 0 < lambdaLocal p := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have h3' : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
  have hnum : 0 < (p : ℚ) - 1 := by linarith
  have hden : 0 < ((p : ℚ) - 2) ^ 2 := by nlinarith
  exact div_pos hnum hden

/-- **`lambdaW_pos`.**  `KERNEL-PROVED`.  λ is strictly positive: every factor comes from an
odd prime, where `(p−1)/(p−2)² > 0`. -/
theorem lambdaW_pos (b : ℕ) : 0 < lambdaW b :=
  Finset.prod_pos fun _p hp => lambdaLocal_pos (oddPrimeFactors_prime hp) (oddPrimeFactors_ne_two hp)

/-- **`lambdaW_ne_zero`.**  `KERNEL-PROVED`. -/
theorem lambdaW_ne_zero (b : ℕ) : lambdaW b ≠ 0 := (lambdaW_pos b).ne'

/-- **`lambdaW_prod_primes`.**  `KERNEL-PROVED`.  The finite prime-product identity: on a
product of distinct odd primes λ is the product of the local factors. -/
theorem lambdaW_prod_primes {t : Finset ℕ} (h : ∀ p ∈ t, p.Prime) (h2 : ∀ p ∈ t, p ≠ 2) :
    lambdaW (∏ p ∈ t, p) = ∏ p ∈ t, lambdaLocal p := by
  classical
  have hpf : (∏ p ∈ t, p).primeFactors = t := Nat.primeFactors_prod h
  have hodd : oddPrimeFactors (∏ p ∈ t, p) = t := by
    rw [oddPrimeFactors, hpf, Finset.erase_eq_of_notMem (fun hmem => h2 2 hmem rfl)]
  rw [lambdaW, hodd]

/-! ## §25.3  Exact local Euler algebra: λ = B0 · β -/

/-- **`lambdaLocal_eq`.**  `KERNEL-PROVED`.  The local factorisation
`(p−1)/(p−2)² = ((p−1)/(p−2)) · (1/(p−2))`. -/
theorem lambdaLocal_eq {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    lambdaLocal p = (((p : ℚ) - 1) / ((p : ℚ) - 2)) * (1 / ((p : ℚ) - 2)) := by
  have hne : ((p : ℚ) - 2) ≠ 0 := sub_two_ne_zero hp h2
  rw [lambdaLocal]
  field_simp

/-- **`lambdaW_eq_B0_mul_beta`.**  `KERNEL-PROVED`.  On odd squarefree arguments the
λ-weight is exactly the `β`-twist of the physical local weight `B0`:

    λ(b) = B0(b) · β(b). -/
theorem lambdaW_eq_B0_mul_beta {b : ℕ} (hsq : Squarefree b) (hodd : ¬ (2 ∣ b)) :
    lambdaW b = B0 b * beta b := by
  have hb0 : b ≠ 0 := by rintro rfl; exact hodd ⟨0, rfl⟩
  have hpf : oddPrimeFactors b = b.primeFactors := by
    rw [oddPrimeFactors, Finset.erase_eq_of_notMem]
    intro hmem
    exact hodd (Nat.dvd_of_mem_primeFactors hmem)
  have hne : ∀ p ∈ b.primeFactors, ((p : ℚ) - 2) ≠ 0 := by
    intro p hp
    refine sub_two_ne_zero (Nat.prime_of_mem_primeFactors hp) ?_
    rintro rfl
    exact hodd (Nat.dvd_of_mem_primeFactors hp)
  rw [lambdaW, hpf, B0, hpf, beta_of_odd_squarefree hsq hodd, one_div, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [lambdaLocal]
  field_simp

/-- The λ-weight of `15 = 3·5`: `2 · (4/9) = 8/9`. -/
@[simp] theorem lambdaW_fifteen : lambdaW 15 = 8 / 9 := by
  rw [lambdaW, oddPrimeFactors_fifteen]
  norm_num [lambdaLocal]

/-! ## §25.4  `H_λ(0) < 8/3`: finite part, analytic tail, conditional combination -/

/-- A finite λ-Euler partial product over a supplied finite set of odd primes and a supplied
local factor function.  This is the only part of an `H_λ`-type quantity that is kernel-owned:
it is a finite product, and nothing about its infinite limit is asserted. -/
def HlambdaFinite (P : Finset ℕ) (loc : ℕ → ℚ) : ℚ := ∏ p ∈ P, loc p

/-- **`HlambdaFinite_split`.**  `KERNEL-PROVED`.  The finite exact product theorem: a partial
product over a disjoint union splits as a product of partial products. -/
theorem HlambdaFinite_split (P Q : Finset ℕ) (loc : ℕ → ℚ) (hPQ : Disjoint P Q) :
    HlambdaFinite (P ∪ Q) loc = HlambdaFinite P loc * HlambdaFinite Q loc := by
  rw [HlambdaFinite, HlambdaFinite, HlambdaFinite, Finset.prod_union hPQ]

/-- **`HlambdaFinite_pos`.**  `KERNEL-PROVED`.  A λ-partial product over odd primes is
positive. -/
theorem HlambdaFinite_pos (P : Finset ℕ) (loc : ℕ → ℚ) (hloc : ∀ p ∈ P, 0 < loc p) :
    0 < HlambdaFinite P loc :=
  Finset.prod_pos hloc

/-- Certificate data for an `H_λ`-type quantity: a kernel-owned finite partial product, an
**analytic tail** that this package does *not* prove anything about, and the total, related
by an explicit hypothesis.  Inhabiting this structure requires supplying the tail estimate;
it is never produced here. -/
structure HLambdaCertificate where
  /-- The finite set of primes carried by the kernel-owned partial product. -/
  primes : Finset ℕ
  /-- The local factor function. -/
  loc : ℕ → ℚ
  /-- The analytic tail contribution (an external, unproved input). -/
  tail : ℚ
  /-- The claimed total. -/
  total : ℚ
  /-- The analytic-tail hypothesis relating total, finite part and tail. -/
  total_eq : total = HlambdaFinite primes loc + tail

/-- **`Hlambda_conditional_bound`.**  `KERNEL-PROVED` (conditional).  If the kernel-owned
finite part plus the supplied analytic tail is below `8/3`, then so is the total.  This is
the only sense in which `H_λ(0) < 8/3` appears in this package: the analytic tail estimate
is an input, never a conclusion. -/
theorem Hlambda_conditional_bound (C : HLambdaCertificate)
    (h : HlambdaFinite C.primes C.loc + C.tail < 8 / 3) : C.total < 8 / 3 := by
  rw [C.total_eq]; exact h

/-- **`Hlambda_not_asserted`.**  `KERNEL-PROVED`.  A firewall: the conditional bound is
vacuous without a tail hypothesis — for every finite part there is a certificate whose total
exceeds `8/3`.  Hence nothing in this file can be read as an unconditional `H_λ(0) < 8/3`. -/
theorem Hlambda_not_asserted (P : Finset ℕ) (loc : ℕ → ℚ) :
    ∃ C : HLambdaCertificate, C.primes = P ∧ C.loc = loc ∧ 8 / 3 < C.total := by
  refine ⟨⟨P, loc, 3 - HlambdaFinite P loc, 3, by ring⟩, rfl, rfl, by norm_num⟩

end Effectivity
end Erdos287
