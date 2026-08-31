import Mathlib

/-!
# V23, §5 — the aggregate Euler local-factor algebra at `w = 0`

`BALANCED7-AGGREGATE-EULER-LOCAL45`

## What is (and is not) formalised

The candidate factorisation of the aggregate Euler product

```
    F_P(w) = ∏_{p ∤ 2P} (1 − 1/((p−1) p^w))  =  H_P(w) / ζ(1+w)
```

is an **analytic** statement about a complex Dirichlet series; this repository has no such
framework, so the factorisation is *not* asserted here.  It is carried as the uninhabited
external interfaces `AggregateEulerPrincipal287Input` and
`AggregateEulerUniformity287Input` at the end of this file.

What *is* formalised — completely, finitely and with no analytic content — is the `w = 0`
Euler-factor algebra that the factorisation would have to reproduce:

```
    off  P :  (1 − 1/(p−1)) / (1 − 1/p)  =  p(p−2)/(p−1)²          (p ≥ 3)
    on   P :               1 / (1 − 1/p)  =  p/(p−1)                (p ≥ 2)
    ratio  :  (on p)/(off p)              =  (p−1)/(p−2)            (p ≥ 3)
```

and the resulting finite identity

```
    H_P(0) = 2·S₂·∏_{p ∣ P, p > 2} (p−1)/(p−2) = 2·B(P),
```

where `S₂` is carried as a *parameter* (the twin-prime constant is an infinite Euler
product, which is exactly the object this repository does not formalise) and `B(P)` is
defined from `S₂` by the displayed finite product.

## Audit status

The independent audit (`OPUS NANC : CASE F — SOURCE-MISSING`) verified
`1/ζ(1+w) = w + O(w²)` but did **not** verify the uniform `H_P(w)` contour estimate.  The
finite algebra below is therefore banked as `LEAN_PROVED`; the uniformity is banked as an
uninhabited interface.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace V23Euler

/-! ## §5.1  The two local factors at `w = 0` -/

/-- The local factor at a prime `p ∤ 2P`: the aggregate factor `1 − 1/((p−1)p^w)` at
`w = 0`, divided by the local factor `1 − 1/p` of `1/ζ(1+w)` at `w = 0`. -/
noncomputable def localFactorOffP (x : ℝ) : ℝ := (1 - 1 / (x - 1)) / (1 - 1 / x)

/-- The local correction at a prime `p ∣ P`: the aggregate factor is absent, so only the
`ζ` factor remains. -/
noncomputable def localFactorOnP (x : ℝ) : ℝ := 1 / (1 - 1 / x)

/-- **`aggregateEuler_localFactor_offP`.**  `LEAN_PROVED`.

For `p > 2`, `p ∤ P`: the local factor is `p(p−2)/(p−1)²`. -/
theorem aggregateEuler_localFactor_offP {x : ℝ} (hx : 3 ≤ x) :
    localFactorOffP x = x * (x - 2) / (x - 1) ^ 2 := by
  have hx0 : x ≠ 0 := by linarith
  have h1 : x - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have h2 : (1 : ℝ) - 1 / x ≠ 0 := by
    have : (1 : ℝ) - 1 / x = (x - 1) / x := by field_simp
    rw [this]
    exact div_ne_zero h1 hx0
  rw [localFactorOffP]
  field_simp
  ring

/-- **`aggregateEuler_localFactor_onP`.**  `LEAN_PROVED`.

For `p ∣ P`: the correction is `p/(p−1)`. -/
theorem aggregateEuler_localFactor_onP {x : ℝ} (hx : 2 ≤ x) :
    localFactorOnP x = x / (x - 1) := by
  have hx0 : x ≠ 0 := by linarith
  have h1 : x - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  rw [localFactorOnP]
  field_simp

/-- **`aggregateEuler_localRatio`.**  `LEAN_PROVED`.

The ratio of the on-`P` correction to the off-`P` factor is `(p−1)/(p−2)`: this single
finite identity is what turns the ambient product `∏_{p>2}` into `S₂` times a divisor
correction over `p ∣ P`. -/
theorem aggregateEuler_localRatio {x : ℝ} (hx : 3 ≤ x) :
    localFactorOnP x / localFactorOffP x = (x - 1) / (x - 2) := by
  have hx0 : x ≠ 0 := by linarith
  have h1 : x - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have h2 : x - 2 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  rw [aggregateEuler_localFactor_onP (by linarith), aggregateEuler_localFactor_offP hx]
  field_simp

/-! ## §5.2  The finite `H_P(0) = 2B(P)` identity -/

/-- The odd prime divisors of `P`. -/
def oddPrimeDivisors (P : ℕ) : Finset ℕ := P.primeFactors.filter (fun p => 2 < p)

theorem three_le_of_mem_oddPrimeDivisors {P p : ℕ} (hp : p ∈ oddPrimeDivisors P) :
    (3 : ℝ) ≤ (p : ℝ) := by
  have h : 2 < p := (Finset.mem_filter.mp hp).2
  exact_mod_cast (by omega : 3 ≤ p)

/-- **`BofP`** — the singular-series datum, defined from the parameter `S₂` by the finite
divisor correction `∏_{p ∣ P, p > 2} (p−1)/(p−2)`. -/
noncomputable def BofP (S2 : ℝ) (P : ℕ) : ℝ :=
  S2 * ∏ p ∈ oddPrimeDivisors P, ((p : ℝ) - 1) / ((p : ℝ) - 2)

/-- **`H0`** — the `w = 0` value of the aggregate numerator, assembled from the local
correction ratios. -/
noncomputable def H0 (S2 : ℝ) (P : ℕ) : ℝ :=
  2 * S2 * ∏ p ∈ oddPrimeDivisors P, (localFactorOnP (p : ℝ) / localFactorOffP (p : ℝ))

/-- **`aggregateEuler_H0_eq_twoB`.**  `LEAN_PROVED`.

The finite identity

```
    H_P(0) = 2·S₂·∏_{p ∣ P, p > 2} (p−1)/(p−2) = 2·B(P).
```

Everything is finite: `S₂` is a parameter, the product ranges over the odd prime divisors
of `P`, and the only mathematical input is the local ratio identity above. -/
theorem aggregateEuler_H0_eq_twoB (S2 : ℝ) (P : ℕ) : H0 S2 P = 2 * BofP S2 P := by
  rw [H0, BofP]
  rw [Finset.prod_congr rfl (fun p hp => aggregateEuler_localRatio
    (three_le_of_mem_oddPrimeDivisors hp))]
  ring

/-- The `p = 2` slot is the source of the factor `2` and of nothing else: with no odd
prime divisors, `H_P(0) = 2 S₂`. -/
theorem aggregateEuler_H0_of_no_odd_divisors {S2 : ℝ} {P : ℕ}
    (hP : oddPrimeDivisors P = ∅) : H0 S2 P = 2 * S2 := by
  rw [H0, hP, Finset.prod_empty, mul_one]

/-! ## §5.3  External analytic interfaces (uninhabited) -/

/-- **`AggregateEulerPrincipal287Input`** — `EXTERNAL / UNINHABITED`.

The literal aggregate statement

```
    J_P(z) = ∑_{q ≤ z, (q,2P)=1} μ(q)/φ(q) · log(z/q) = 2B(P) + O_A(log^{-A} z)
```

uniformly for the physical seven-prime family.  Carried with the audit-mandated metadata
fields.  **No inhabitant is constructed.** -/
structure AggregateEulerPrincipal287Input
    (J : ℕ → ℝ → ℝ) (S2 : ℝ) (family : Finset ℕ) (Aexp : ℝ) (effective : Bool) : Prop where
  /-- The `q`-cells summed by `J` are exactly the literal ones:
  `J_P(z) = ∑_{q ≤ z, (q,2P)=1} μ(q)/φ(q) · log(z/q)`. -/
  q_partition_compatible : ∀ P ∈ family, ∀ z : ℝ, 2 ≤ z →
    J P z = ∑ q ∈ (Finset.Icc 1 ⌊z⌋₊).filter (fun q => Nat.Coprime q (2 * P)),
      (ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) * Real.log (z / q)
  /-- The error bound, uniform in `P` over the physical family. -/
  uniform_in_P : ∀ P ∈ family, ∀ z : ℝ, 2 ≤ z →
    |J P z - 2 * BofP S2 P| ≤ (Real.log z) ^ (-Aexp)
  /-- Repeated primes in the seven-prime vector are handled by the same statement: the
  aggregate depends on `P` only through its radical. -/
  repeated_primes : ∀ P ∈ family, ∀ z : ℝ, 2 ≤ z → J P z = J (∏ p ∈ P.primeFactors, p) z
  /-- The declared log saving is positive. -/
  saving_positive : 0 < Aexp

/-- **`AggregateEulerUniformity287Input`** — `EXTERNAL / UNINHABITED / SOURCE-MISSING`.

The item the independent audit lists as *not verified*: the uniform contour estimate for
`H_P(w)` behind the factorisation `F_P(w) = H_P(w)/ζ(1+w)`.

Fields: the factorisation itself, an explicit uniform bound on `H_P(w)` on the contour
region, the physical family, the contour, a fixed sufficient log saving `A₀`, and the
resulting `J_P(z) − 2B(P)` bound. -/
structure AggregateEulerUniformity287Input
    (F H : ℕ → ℂ → ℂ) (zetaInv : ℂ → ℂ) (J : ℕ → ℝ → ℝ) (S2 : ℝ)
    (family : Finset ℕ) (contour : Set ℂ) (Hbound A0 : ℝ) : Prop where
  /-- `F_P(w) = H_P(w)/ζ(1+w)` on the contour region. -/
  factorisation : ∀ P ∈ family, ∀ w ∈ contour, F P w = H P w * zetaInv w
  /-- An explicit bound on `H_P(w)`, uniform in `P` and in `w` on the contour. -/
  uniform_H_bound : ∀ P ∈ family, ∀ w ∈ contour, ‖H P w‖ ≤ Hbound
  /-- The contour is nonempty (a genuine region). -/
  contour_nonempty : contour.Nonempty
  /-- The fixed sufficient log saving. -/
  saving_positive : 0 < A0
  /-- The resulting aggregate bound. -/
  aggregate_bound : ∀ P ∈ family, ∀ z : ℝ, 2 ≤ z →
    |J P z - 2 * BofP S2 P| ≤ Hbound * (Real.log z) ^ (-A0)

/-- **`aggregateEulerPrincipal_not_automatic`.**  `LEAN_PROVED`. -/
theorem aggregateEulerPrincipal_not_automatic :
    ∃ (J : ℕ → ℝ → ℝ) (S2 : ℝ) (family : Finset ℕ) (Aexp : ℝ) (effective : Bool),
      ¬ AggregateEulerPrincipal287Input J S2 family Aexp effective := by
  refine ⟨fun _ _ => 0, 0, ∅, -1, true, ?_⟩
  intro h
  exact absurd h.saving_positive (by norm_num)

/-- **`aggregateEulerUniformity_not_automatic`.**  `LEAN_PROVED`. -/
theorem aggregateEulerUniformity_not_automatic :
    ∃ (F H : ℕ → ℂ → ℂ) (zetaInv : ℂ → ℂ) (J : ℕ → ℝ → ℝ) (S2 : ℝ)
      (family : Finset ℕ) (contour : Set ℂ) (Hbound A0 : ℝ),
      ¬ AggregateEulerUniformity287Input F H zetaInv J S2 family contour Hbound A0 := by
  refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ _ => 0, 0, ∅, ∅, 0, 1, ?_⟩
  intro h
  exact absurd h.contour_nonempty (by simp)

end V23Euler
end Erdos287
