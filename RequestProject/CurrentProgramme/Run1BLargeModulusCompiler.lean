import RequestProject.CurrentProgramme.Run1BResidueClassEnergy

/-!
# RUN1B / d*wp provider — §5  the large-effective-modulus compiler

```
residue-class energy + range inequalities  →  contraction expression : CONDITIONAL KERNEL-PROVED
"the contraction is not a log-saving"                                : KERNEL-PROVED COUNTERGUARD
```

The implication proved here is purely algebraic: every analytic ingredient (the coefficient
energies `EX`, `EY`, the class multiplicities, the physical exponent ranges) enters as an
**explicit hypothesis**.  Nothing in this file asserts an arbitrary-log saving, and the final
counterguard shows that the contraction conclusion by itself does not deliver one.

This module is **append-only** and project-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Run1B
namespace LargeModulus

open Run1B.ResidueEnergy

/-- **`largeModulus_contraction`.**  `CONDITIONAL KERNEL-PROVED`.

From
* the finite `L²` bilinear bound `|S| ≤ √n · NX · NY` (§4, kernel-proved),
* the residue-class energy bounds `NX² ≤ (1 + D/n) EX`, `NY² ≤ (1 + W/n) EY`,

one obtains the displayed source-specific contraction

```
|S|²  ≤  (n + D)(n + W)/n · EX · EY .
```

No analytic input is used: `EX`, `EY` are hypotheses. -/
theorem largeModulus_contraction {S n D W EX EY NX NY : ℝ} (hn : 0 < n) (hD : 0 ≤ D)
    (hW : 0 ≤ W) (hNX : 0 ≤ NX) (hNY : 0 ≤ NY) (hS0 : 0 ≤ S)
    (hS : S ≤ Real.sqrt n * NX * NY)
    (hX : NX ^ 2 ≤ (1 + D / n) * EX) (hY : NY ^ 2 ≤ (1 + W / n) * EY)
    (hEY : 0 ≤ EY) :
    S ^ 2 ≤ (n + D) * (n + W) / n * EX * EY := by
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (le_of_lt hn)
  have hsqrt_nonneg : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  have h1 : S ^ 2 ≤ (Real.sqrt n * NX * NY) ^ 2 := by
    have hpos : 0 ≤ Real.sqrt n * NX * NY := by positivity
    nlinarith [hS, hS0, hpos]
  have h2 : (Real.sqrt n * NX * NY) ^ 2 = n * (NX ^ 2 * NY ^ 2) := by
    rw [mul_pow, mul_pow, hsq]
    ring
  have h3 : NX ^ 2 * NY ^ 2 ≤ ((1 + D / n) * EX) * ((1 + W / n) * EY) := by
    have hX0 : 0 ≤ NX ^ 2 := sq_nonneg NX
    have hY0 : 0 ≤ NY ^ 2 := sq_nonneg NY
    have hb : 0 ≤ (1 + W / n) * EY := by
      have : 0 ≤ 1 + W / n := by positivity
      exact mul_nonneg this hEY
    calc NX ^ 2 * NY ^ 2 ≤ ((1 + D / n) * EX) * NY ^ 2 := by nlinarith
      _ ≤ ((1 + D / n) * EX) * ((1 + W / n) * EY) := by nlinarith [hY, hX0, hY0]
  have h4 : n * (NX ^ 2 * NY ^ 2) ≤ n * (((1 + D / n) * EX) * ((1 + W / n) * EY)) := by
    exact mul_le_mul_of_nonneg_left h3 (le_of_lt hn)
  have h5 : n * (((1 + D / n) * EX) * ((1 + W / n) * EY))
      = (n + D) * (n + W) / n * EX * EY := by
    field_simp
  calc S ^ 2 ≤ (Real.sqrt n * NX * NY) ^ 2 := h1
    _ = n * (NX ^ 2 * NY ^ 2) := h2
    _ ≤ n * (((1 + D / n) * EX) * ((1 + W / n) * EY)) := h4
    _ = (n + D) * (n + W) / n * EX * EY := h5

/-- **`contraction_is_not_a_log_saving`.**  `KERNEL-PROVED` counterguard.

The contraction conclusion of `largeModulus_contraction` is compatible with an arbitrarily
large sum: at `n = 1`, `D = W = 0`, `EX = EY = 100`, `NX = NY = 10`, all hypotheses hold with
`S = 10`.  Hence the algebraic compiler alone never yields a saving; a saving requires the
analytic energy inputs to be supplied and to be small. -/
theorem contraction_is_not_a_log_saving :
    ∃ S n D W EX EY NX NY : ℝ, 0 < n ∧ 0 ≤ D ∧ 0 ≤ W ∧ 0 ≤ NX ∧ 0 ≤ NY ∧ 0 ≤ S ∧
      S ≤ Real.sqrt n * NX * NY ∧ NX ^ 2 ≤ (1 + D / n) * EX ∧ NY ^ 2 ≤ (1 + W / n) * EY ∧
      0 ≤ EX ∧ 0 ≤ EY ∧ 1 < S := by
  refine ⟨10, 1, 0, 0, 100, 100, 10, 10, by norm_num, le_refl 0, le_refl 0, by norm_num,
    by norm_num, by norm_num, ?_, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩
  rw [Real.sqrt_one]
  norm_num

end LargeModulus
end Run1B
