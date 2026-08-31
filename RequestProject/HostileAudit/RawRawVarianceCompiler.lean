import Mathlib
import RequestProject.HostileAudit.ShiuHypothesisCompiler

/-!
# Hostile-audit safe bank §10 — raw-raw / principal / cross variance compiler

A **source-neutral** variance compiler in explicit normalised variables.  The inputs are the
declared norms

```
‖α‖₂²  ≤ M · log^{-2},
‖c‖₁   ≤ W₅ · log^{-5},
‖c‖₂²  ≤ W₅ · log^{-5},
```

together with the (uninhabited) short-`t` sieve and Shiu interfaces, and the *assembly law*
supplied by the source

```
V_RR ≤ (M/Q) · ‖c‖₁ · W₅.
```

The conclusion is

```
V_RR ≤ (M·W₅²/Q) · log^{-5}.
```

**The saving is `log^{-5}`, not `log^{-10}`.**  One copy of the coefficient spends its `L¹`
mass; the other copy is consumed by the `t`-sieve and carries no logarithmic saving.  This is
enforced here by a *proved refutation*: `rawRaw_saving_is_five_not_ten` exhibits admissible
data for which the `log^{-10}` bound is false.

The Cauchy–Schwarz compiler for the principal and cross terms is banked separately:

```
V_PP ≤ natural · log^{-10},     V_RP ≤ √(V_RR·V_PP) ≤ natural · log^{-15/2}.
```
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace HostileAudit

/-! ## §10.1  The raw-raw inputs -/

/-- **`RawRawVarianceInputs`** — the source-neutral raw-raw bundle.

`L` is the abstract logarithm (`L = log X` in the application); `alpha2`, `c1`, `c2` are the
declared norms; `shortT` and `shiu` are the two external Props (the banked uninhabited
interfaces in the application).  The field `assembly` is the *source law* — it is an
assumption about the supplied data, never a theorem of this module. -/
structure RawRawVarianceInputs (M W5 Q L alpha2 c1 c2 VRR : ℝ) (shortT shiu : Prop) : Prop where
  /-- The abstract logarithm is `> 1`. -/
  L_gt_one : 1 < L
  /-- The modulus scale is positive. -/
  Q_pos : 0 < Q
  /-- The outer scale is nonnegative. -/
  M_nonneg : 0 ≤ M
  /-- The inner scale is nonnegative. -/
  W5_nonneg : 0 ≤ W5
  /-- The `L¹` mass is nonnegative. -/
  c1_nonneg : 0 ≤ c1
  /-- Outer energy: `‖α‖₂² ≤ M·log^{-2}`. -/
  alpha_energy : alpha2 ≤ M / L ^ 2
  /-- Coefficient `L¹` mass: `‖c‖₁ ≤ W₅·log^{-5}`. -/
  c1_mass : c1 ≤ W5 / L ^ 5
  /-- Coefficient `L²` energy: `‖c‖₂² ≤ W₅·log^{-5}`. -/
  c2_energy : c2 ≤ W5 / L ^ 5
  /-- The short-`t` sieve input. -/
  short_t : shortT
  /-- The Shiu input. -/
  shiu : shiu
  /-- The source assembly law: one copy spends `L¹` mass, the other is consumed by the
  `t`-sieve. -/
  assembly : VRR ≤ M / Q * c1 * W5

/-- **`rawRaw_variance_bound`.**  `CONDITIONAL_COMPILER / LEAN_PROVED`.

```
V_RR ≤ (M·W₅²/Q)·log^{-5}.
```
-/
theorem rawRaw_variance_bound {M W5 Q L alpha2 c1 c2 VRR : ℝ} {shortT shiu : Prop}
    (h : RawRawVarianceInputs M W5 Q L alpha2 c1 c2 VRR shortT shiu) :
    VRR ≤ M * W5 ^ 2 / Q / L ^ 5 := by
  have hL : (0 : ℝ) < L := lt_trans zero_lt_one h.L_gt_one
  have hMQ : 0 ≤ M / Q := div_nonneg h.M_nonneg h.Q_pos.le
  have h1 : M / Q * c1 * W5 ≤ M / Q * (W5 / L ^ 5) * W5 := by
    have := mul_le_mul_of_nonneg_left h.c1_mass hMQ
    exact mul_le_mul_of_nonneg_right this h.W5_nonneg
  have h2 : M / Q * (W5 / L ^ 5) * W5 = M * W5 ^ 2 / Q / L ^ 5 := by
    field_simp
  calc VRR ≤ M / Q * c1 * W5 := h.assembly
    _ ≤ M / Q * (W5 / L ^ 5) * W5 := h1
    _ = M * W5 ^ 2 / Q / L ^ 5 := h2

/-- **`rawRaw_saving_is_five_not_ten`.**  `LEAN_PROVED`.

The hostile audit's correction, as a theorem: the raw-raw saving is `log^{-5}` and the
`log^{-10}` claim is **false**.  Explicit admissible data (`M = W₅ = Q = 1`, `L = 2`,
`‖c‖₁ = ‖c‖₂² = 1/32`, `V_RR = 1/32`) satisfy every input while violating the `log^{-10}`
bound. -/
theorem rawRaw_saving_is_five_not_ten :
    ∃ (M W5 Q L alpha2 c1 c2 VRR : ℝ),
      RawRawVarianceInputs M W5 Q L alpha2 c1 c2 VRR True True ∧
        VRR ≤ M * W5 ^ 2 / Q / L ^ 5 ∧
        ¬ (VRR ≤ M * W5 ^ 2 / Q / L ^ 10) := by
  refine ⟨1, 1, 1, 2, 0, 1 / 32, 1 / 32, 1 / 32, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial,
    trivial, ?_⟩, ?_, ?_⟩ <;> norm_num

/-! ## §10.2  The Cauchy–Schwarz cross compiler -/

/-- **`cross_variance_bound`.**  `LEAN_PROVED`.

The Cauchy compiler: from `V_RP² ≤ V_RR·V_PP`, `V_RR ≤ A·log^{-5}` and
`V_PP ≤ B·log^{-10}`,

```
V_RP ≤ √(A·B) · log^{-15/2}.
```
-/
theorem cross_variance_bound {A B L VRR VPP VRP : ℝ}
    (hL : 0 < L) (hVRP : 0 ≤ VRP) (hVPP : 0 ≤ VPP)
    (hcs : VRP ^ 2 ≤ VRR * VPP)
    (hRR : VRR ≤ A / L ^ 5) (hPP : VPP ≤ B / L ^ 10) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    VRP ≤ Real.sqrt (A * B) / L ^ ((15 : ℝ) / 2) := by
  have hABL : (0 : ℝ) ≤ A * B / L ^ 15 := by positivity
  have hstep : VRP ^ 2 ≤ A * B / L ^ 15 := by
    have h1 : VRR * VPP ≤ A / L ^ 5 * (B / L ^ 10) := by
      apply mul_le_mul hRR hPP hVPP
      positivity
    have h2 : A / L ^ 5 * (B / L ^ 10) = A * B / L ^ 15 := by field_simp
    linarith
  have hsq : VRP ≤ Real.sqrt (A * B / L ^ 15) := (Real.le_sqrt hVRP hABL).2 hstep
  have hdiv : Real.sqrt (A * B / L ^ 15) = Real.sqrt (A * B) / L ^ ((15 : ℝ) / 2) := by
    rw [Real.sqrt_div (by positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast L 15, ← Real.rpow_mul hL.le]
    norm_num
  linarith [hdiv ▸ hsq]

/-! ## §10.3  The exponent ledger -/

/-- The raw-raw log exponent (`−5`), the principal one (`−10`) and the cross one (`−15/2`). -/
def rawRawLogExponent : ℚ := -5

/-- The principal-principal log exponent. -/
def principalLogExponent : ℚ := -10

/-- The cross log exponent. -/
def crossLogExponent : ℚ := -15 / 2

/-- **`variance_exponent_ledger`.**  `LEAN_PROVED` (rational arithmetic).

The cross exponent is the Cauchy mean of the other two, and the raw-raw exponent is *not*
the principal one. -/
theorem variance_exponent_ledger :
    crossLogExponent = (rawRawLogExponent + principalLogExponent) / 2 ∧
      rawRawLogExponent ≠ principalLogExponent ∧
      principalLogExponent < crossLogExponent ∧
      crossLogExponent < rawRawLogExponent := by
  unfold crossLogExponent rawRawLogExponent principalLogExponent
  norm_num

end HostileAudit
end Erdos287
