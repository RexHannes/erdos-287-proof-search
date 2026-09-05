import Mathlib

/-!
# Erdős #287 effectivity — the ratio-boundary form (§14)

```
RATIO-BOUNDARY : KERNEL-PROVED (conditional on the two cancellations, as requested)
```

Taking the discrete splice of §10 and the continuous splice of §11 and *using* the two
cancellations

* the full odd discrete line cancellation (§12), `∑_d μ(d)·(odd line) = 0`, and
* the continuous coefficient cancellation (§13), `∑_d μ(d)·M_d·∫_0^∞ = 0`,

the difference `F₁ − F₂` is transformed into the **ratio-boundary form**

    F₁ − F₂ = ∑_d μ(d) [ −∑_{n ≤ d, n odd} A_d(n)W(dn/X)
                         + (M_d/2)∫_0^d W(dt/X)dt
                         + ∑_{d < n ≤ 4d, n even} A_d(n)W(dn/X)
                         − (M_d/2)∫_d^{4d} W(dt/X)dt ].

The theorem below is the exact algebraic transformation, with the two cancellations as
explicit hypotheses (the continuous one is analytic and is **not** proved anywhere in this
package).  `mu`, `oddLow`, `oddHigh`, `evenMid`, `M`, `I0d`, `Idinf`, `Imid` are the
per-`d` data: the odd sum below/above `d`, the even collar sum, the source factor
`M_d = d/φ(d) − B1`, and the three integrals `∫_0^d`, `∫_d^∞`, `∫_d^{4d}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-- **`ratio_boundary_form`.**  `KERNEL-PROVED`, conditional on the two cancellations.

The left-hand side is `(D₁ − D₂) − (C₁ − C₂)` written per `d`; the right-hand side is the
ratio-boundary form. -/
theorem ratio_boundary_form (Dset : Finset ℕ)
    (mu oddLow oddHigh evenMid M I0d Idinf Imid : ℕ → ℝ)
    (hdiscrete : ∑ d ∈ Dset, mu d * (oddLow d + oddHigh d) = 0)
    (hcontinuous : ∑ d ∈ Dset, mu d * M d * (I0d d + Idinf d) = 0) :
    (∑ d ∈ Dset, mu d * oddHigh d) + (∑ d ∈ Dset, mu d * evenMid d)
        - (1 / 2) * (∑ d ∈ Dset, mu d * M d * Idinf d)
        - (1 / 2) * (∑ d ∈ Dset, mu d * M d * Imid d)
      = - (∑ d ∈ Dset, mu d * oddLow d)
        + (1 / 2) * (∑ d ∈ Dset, mu d * M d * I0d d)
        + (∑ d ∈ Dset, mu d * evenMid d)
        - (1 / 2) * (∑ d ∈ Dset, mu d * M d * Imid d) := by
  have h1 : (∑ d ∈ Dset, mu d * oddLow d) + ∑ d ∈ Dset, mu d * oddHigh d = 0 := by
    rw [← Finset.sum_add_distrib]
    rw [← hdiscrete]
    exact Finset.sum_congr rfl fun d _ => by ring
  have h2 : (∑ d ∈ Dset, mu d * M d * I0d d) + ∑ d ∈ Dset, mu d * M d * Idinf d = 0 := by
    rw [← Finset.sum_add_distrib]
    rw [← hcontinuous]
    exact Finset.sum_congr rfl fun d _ => by ring
  linarith

end Effectivity
end Erdos287
