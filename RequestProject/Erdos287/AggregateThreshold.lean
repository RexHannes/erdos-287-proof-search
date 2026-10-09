import Mathlib

/-!
# Erdős #287 effectivity — aggregate threshold arithmetic and the remainder ledger (§27)

```
AGGREGATE THRESHOLD ARITHMETIC : KERNEL-PROVED
ENDPOINT BUDGET CONSTANTS      : DIRECTED CERTIFICATE DATA
69/5000 − 469/75000 = 283/37500: KERNEL-PROVED
F/ED/DD/S REMAINDER TYPE       : KERNEL-PROVED
C_rem < 283/37500              : OPEN (stated, deliberately unproved)
C_agg ≤ 69/5000                : OPEN (stated, deliberately unproved)
```

Only *arithmetic* is banked here.  The λ-weighted aggregate covariance bound
`C_agg ≤ 69/5000` is **not** asserted: it appears solely as the hypothesis of a conditional
statement placing the aggregate constant below the supplied critical value `0.01382165`.
Likewise the endpoint budget constants are directed certificate data, and the remaining
covariance target `C_F + 2C_ED + C_DD + C_S < 283/37500` is stated as a goal with no proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Effectivity

/-! ## §27.1  The aggregate threshold -/

/-- The sufficient target for the λ-weighted aggregate square-function constant:
`C_agg_target = 69/5000`.  **Banked as arithmetic data, not as an achieved estimate.** -/
def CAggTarget : ℚ := 69 / 5000

/-- The supplied critical value `0.01382165…` below which the aggregate constant must lie. -/
def CAggCritical : ℚ := 1382165 / 10 ^ 8

/-- The λ-weighted aggregate covariance bound, as a *predicate* on a supplied constant.
Nothing in this package inhabits it for the physical constant. -/
def CAggBound (Cagg : ℚ) : Prop := Cagg ≤ CAggTarget

/-- **`CAggTarget_lt_critical`.**  `KERNEL-PROVED`.  `69/5000 = 0.0138 < 0.01382165`. -/
theorem CAggTarget_lt_critical : CAggTarget < CAggCritical := by
  rw [CAggTarget, CAggCritical]; norm_num

/-- **`CAgg_below_critical_of_target`.**  `KERNEL-PROVED` (conditional).  *If* the
λ-weighted square-function constant satisfies `C_agg ≤ 69/5000`, *then* it lies below the
supplied critical value `0.01382165…`.  The hypothesis is an open analytic input. -/
theorem CAgg_below_critical_of_target {Cagg : ℚ} (h : CAggBound Cagg) : Cagg < CAggCritical :=
  lt_of_le_of_lt h CAggTarget_lt_critical

/-- **`CAggBound_not_proved`.**  `KERNEL-PROVED`.  A firewall: `CAggBound` is a nontrivial
predicate (it fails for some constants), so its appearance as a hypothesis above cannot be
read as an achieved estimate. -/
theorem CAggBound_not_proved : ¬ CAggBound 1 := by
  rw [CAggBound, CAggTarget]; norm_num

/-! ## §27.2  Endpoint budget constants (directed certificate data) -/

/-- `C_end_period_upper = 469/75000`: the complete-period endpoint budget line. -/
def CEndPeriodUpper : ℚ := 469 / 75000

/-- `C_end_diag_upper = 47/10000`: the diagonal endpoint budget line. -/
def CEndDiagUpper : ℚ := 47 / 10000

/-- `C_end_off_upper = 17/10000`: the off-diagonal endpoint budget line. -/
def CEndOffUpper : ℚ := 17 / 10000

/-- The remaining covariance target `283/37500`. -/
def CRemTarget : ℚ := 283 / 37500

/-- **`aggregate_minus_endpoint`.**  `KERNEL-PROVED`.

    69/5000 − 469/75000 = 283/37500. -/
theorem aggregate_minus_endpoint : CAggTarget - CEndPeriodUpper = CRemTarget := by
  rw [CAggTarget, CEndPeriodUpper, CRemTarget]; norm_num

/-- **`endpoint_budget_positive`.**  `KERNEL-PROVED`.  All banked endpoint budget lines are
positive and strictly below the aggregate target. -/
theorem endpoint_budget_positive :
    0 < CEndPeriodUpper ∧ 0 < CEndDiagUpper ∧ 0 < CEndOffUpper ∧ CEndPeriodUpper < CAggTarget := by
  refine ⟨by rw [CEndPeriodUpper]; norm_num, by rw [CEndDiagUpper]; norm_num,
    by rw [CEndOffUpper]; norm_num, ?_⟩
  rw [CEndPeriodUpper, CAggTarget]; norm_num

/-- **`diag_off_not_period`.**  `KERNEL-PROVED`.  A bookkeeping firewall: the diagonal and
off-diagonal endpoint lines do **not** add up to the complete-period line —
`47/10000 + 17/10000 = 64/10000 > 469/75000` — so they are separate certificate lines and
may not be substituted for the period constant. -/
theorem diag_off_not_period : CEndPeriodUpper < CEndDiagUpper + CEndOffUpper := by
  rw [CEndPeriodUpper, CEndDiagUpper, CEndOffUpper]; norm_num

/-! ## §27.3  The remaining covariance components F / ED / DD / S -/

/-- The four remainder components of the long-fibre covariance:

* `F`  — finite-period / hyperbola truncation;
* `ED` — endpoint-derivative;
* `DD` — derivative-derivative;
* `S`  — lattice / no-lattice splice. -/
structure RemainderComponents where
  /-- Finite-period / hyperbola truncation. -/
  F : ℚ
  /-- Endpoint-derivative. -/
  ED : ℚ
  /-- Derivative-derivative. -/
  DD : ℚ
  /-- Lattice / no-lattice splice. -/
  S : ℚ

/-- The combined remaining covariance constant `C_rem = C_F + 2 C_ED + C_DD + C_S`. -/
def CRem (R : RemainderComponents) : ℚ := R.F + 2 * R.ED + R.DD + R.S

/-- **`CRem_eq`.**  `KERNEL-PROVED`.  The algebraic combination law — the only content of
this section that is proved. -/
theorem CRem_eq (R : RemainderComponents) : CRem R = R.F + 2 * R.ED + R.DD + R.S := rfl

/-- **`CRem_le_of_components`.**  `KERNEL-PROVED`.  Componentwise certificates combine
additively. -/
theorem CRem_le_of_components (R : RemainderComponents) {f ed dd s : ℚ}
    (hF : R.F ≤ f) (hED : R.ED ≤ ed) (hDD : R.DD ≤ dd) (hS : R.S ≤ s) :
    CRem R ≤ f + 2 * ed + dd + s := by
  rw [CRem]; linarith

/-- The remaining covariance target as a proposition: `C_rem < 283/37500`.
**Status: OPEN.**  No proof of this is provided anywhere in this package. -/
def RemainingCovarianceTargetMet (R : RemainderComponents) : Prop := CRem R < CRemTarget

/-- **`remaining_target_not_proved`.**  `KERNEL-PROVED`.  A firewall: the remaining
covariance target genuinely fails for some component data, so it is a real open goal and not
a tautology. -/
theorem remaining_target_not_proved :
    ¬ RemainingCovarianceTargetMet ⟨1, 0, 0, 0⟩ := by
  rw [RemainingCovarianceTargetMet, CRem, CRemTarget]; norm_num

/-- **`aggregate_closure_conditional`.**  `KERNEL-PROVED` (conditional).  The arithmetic of
the closure: if the endpoint line is certified at `469/75000`, the remaining covariance meets
its target `283/37500`, and the aggregate constant splits as endpoint + remainder, then the
aggregate target `69/5000` is met.  Both hypotheses are open analytic inputs. -/
theorem aggregate_closure_conditional {Cend Cagg : ℚ} (R : RemainderComponents)
    (hend : Cend ≤ CEndPeriodUpper) (hrem : RemainingCovarianceTargetMet R)
    (hsplit : Cagg = Cend + CRem R) : Cagg < CAggTarget := by
  rw [RemainingCovarianceTargetMet] at hrem
  rw [hsplit]
  have := aggregate_minus_endpoint
  linarith

end Effectivity
end Erdos287
