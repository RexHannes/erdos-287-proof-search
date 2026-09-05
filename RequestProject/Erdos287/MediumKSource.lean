import Mathlib
import RequestProject.Erdos287.GcdDescent
import RequestProject.Erdos287.BernoulliKernel

/-!
# Erdős #287 — the exact medium-`k` squarefree source normal form

```
MEDIUM-k EXACT SOURCE NORMAL FORM : KERNEL-PROVED (conditional on the finite
                                    truncation `U`, `K` of the source support)
DESCENDED SUPPORT WINDOW          : KERNEL-PROVED (mediumKWeight_descended)
DESCENDED PHASE                   : KERNEL-PROVED (jointKernel_phase_descent)
```

The medium-`k` operator is *defined* as a finite sum over truncations `U` (the `u`-support)
and `K` (the `k`-support).  Both the `k > 31` cut and the hyperbolic cut `k·u ≤ (9/10)X/c`
are folded into the weight `mediumKWeight`, so the reindexing is an instance of
`squarefree_gcd_descent_real`.  **No analytic bound for `Rmed` is proved or claimed.**

The decimal `0.9` is always the exact rational `9/10`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset ArithmeticFunction Erdos287.SourceWeights Erdos287.GcdDescent
open Erdos287.BernoulliKernel

namespace Erdos287
namespace MediumKSource

/-- The medium-`k` weight: the joint Bernoulli kernel restricted to the medium-`k` window
`k > 31` and to the hyperbolic support `k·u ≤ (9/10)·X/c`. -/
noncomputable def mediumKWeight (W W' : ℝ → ℝ) (X : ℝ) (c u k : ℕ) : ℝ :=
  if 31 < k ∧ ((k * u : ℕ) : ℝ) ≤ (9 / 10) * X / (c : ℝ) then
    jointKernel W W' X ((c * u : ℕ) : ℝ) ((k : ℕ) : ℝ)
  else 0

/-- The **original** coprime squarefree medium-`k` source operator. -/
noncomputable def RmedSource (W W' : ℝ → ℝ) (S2 : ℚ) (X : ℝ) (eps : ℕ → ℝ)
    (U K : Finset ℕ) : ℝ :=
  -4 * ∑ c ∈ ({1, 2} : Finset ℕ), eps c *
    ∑ u ∈ U, ∑ k ∈ K, (if Nat.Coprime u k then (1 : ℝ) else 0) *
      ((((moebius u : ℚ) * Bsrc S2 u * beta k : ℚ) : ℝ) * mediumKWeight W W' X c u k)

/-- The **descended** (gcd-descent) medium-`k` source operator. -/
noncomputable def Rmed (W W' : ℝ → ℝ) (S2 : ℚ) (X : ℝ) (eps : ℕ → ℝ)
    (U K : Finset ℕ) : ℝ :=
  -4 * ∑ c ∈ ({1, 2} : Finset ℕ), eps c *
    ∑ t ∈ descentIndex U K,
      (((lam t.1 * beta t.2.1 * (moebius t.2.2 : ℚ) * Bsrc S2 t.2.2 : ℚ) : ℝ)) *
        mediumKWeight W W' X c (t.1 * t.2.2) (t.1 * t.2.1)

/-- **`mediumK_source_normal_form`.** `KERNEL-PROVED`.  The descended operator is *exactly*
the reindexed original coprime squarefree operator, for every finite truncation `U`, `K`
consisting of nonzero squarefree moduli. -/
theorem mediumK_source_normal_form (W W' : ℝ → ℝ) (S2 : ℚ) (X : ℝ) (eps : ℕ → ℝ)
    {U K : Finset ℕ} (hU0 : 0 ∉ U) (hK0 : 0 ∉ K)
    (hUsf : ∀ u ∈ U, Squarefree u) (hKsf : ∀ k ∈ K, Squarefree k) :
    Rmed W W' S2 X eps U K = RmedSource W W' S2 X eps U K := by
  unfold Rmed RmedSource
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact (squarefree_gcd_descent_real S2 (fun u k => mediumKWeight W W' X c u k)
    hU0 hK0 hUsf hKsf).symm

/-- **`mediumKWeight_descended`.** `KERNEL-PROVED`.  In the descended variables `u = bv`,
`k = bq` the support window becomes `bq > 31` and `b²qv ≤ (9/10)·X/c`. -/
theorem mediumKWeight_descended (W W' : ℝ → ℝ) (X : ℝ) (c b q v : ℕ) :
    mediumKWeight W W' X c (b * v) (b * q)
      = if 31 < b * q ∧ ((b ^ 2 * q * v : ℕ) : ℝ) ≤ (9 / 10) * X / (c : ℝ) then
          jointKernel W W' X ((c * (b * v) : ℕ) : ℝ) ((b * q : ℕ) : ℝ)
        else 0 := by
  rw [mediumKWeight, hyperbola_support_gcd_descent_nat b q v]

/-- **`Rmed_descended_window`.** `KERNEL-PROVED`.  The medium-`k` operator written out in the
descended normal form requested by the source bank. -/
theorem Rmed_descended_window (W W' : ℝ → ℝ) (S2 : ℚ) (X : ℝ) (eps : ℕ → ℝ)
    (U K : Finset ℕ) :
    Rmed W W' S2 X eps U K
      = -4 * ∑ c ∈ ({1, 2} : Finset ℕ), eps c *
          ∑ t ∈ descentIndex U K,
            (((lam t.1 * beta t.2.1 * (moebius t.2.2 : ℚ) * Bsrc S2 t.2.2 : ℚ) : ℝ)) *
              (if 31 < t.1 * t.2.1 ∧
                    ((t.1 ^ 2 * t.2.1 * t.2.2 : ℕ) : ℝ) ≤ (9 / 10) * X / (c : ℝ) then
                jointKernel W W' X ((c * (t.1 * t.2.2) : ℕ) : ℝ) ((t.1 * t.2.1 : ℕ) : ℝ)
              else 0) := by
  unfold Rmed
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mediumKWeight_descended]

/-- **`jointKernel_phase_descent`.** `KERNEL-PROVED`.  The sawtooth phase of the descended
endpoint term only sees `c·v/q`: the `b`-factor cancels. -/
theorem jointKernel_phase_descent (c b q v : ℝ) (hb : b ≠ 0) (hq : q ≠ 0) :
    psi (c * (b * v) / (b * q)) = psi (c * v / q) :=
  phase_descent_apply psi c b q v hb hq

/-- The descended `W`-argument: `(c·u)²/X = c²b²v²/X`. -/
theorem jointKernel_W_argument_descent (c b v X : ℝ) :
    (c * (b * v)) ^ 2 / X = c ^ 2 * b ^ 2 * v ^ 2 / X :=
  W_argument_descent c b v X

/-- The descended derivative argument: `X·y/(c·k·u) = X·y/(c·b²·q·v)`. -/
theorem jointKernel_derivative_argument_descent (X y c b q v : ℝ) :
    X * y / (c * (b * q) * (b * v)) = X * y / (c * b ^ 2 * q * v) :=
  derivative_argument_descent X y c b q v

end MediumKSource
end Erdos287
