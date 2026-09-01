import Mathlib
import RequestProject.Erdos287.FixedCertificateLeakageCompiler
import RequestProject.Erdos287.FixedCertificateFordData

/-!
# The FCL algebraic bridge, the comparison-margin firewall and the `N2` separation

`FCL : CONDITIONAL`

The banked compiler `Erdos287.FixedCertificate.fixedCertificate_prime_mass_pos` needs its
error hypothesis in the *relative* form `E ≤ δ·B`.  The analytic side, however, produces
absolute scalings

```
    B ≥ cB · X / log X,          E ≤ cE · X / (log X)^{1+η},        cB > 0,  η > 0.
```

`fcl_relative_error_of_scaling` is the generic algebraic bridge between the two, with the
threshold hypothesis kept **completely explicit**:

```
    cE ≤ δ · cB · (log X)^η .
```

Nothing asymptotic is hidden: every hypothesis is an antecedent, and no scaling constant is
supplied.  `Erdos287.FordData.CertificatePinned` and
`Erdos287.FordData.PositiveComparisonMargin` are **not** inhabited; §3 only exposes the
finite arithmetic that follows *if* a positive margin is supplied.  §4 keeps the `N2` slack
strictly additive.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace FCLBridge

open Erdos287.FixedCertificate
open Erdos287.FixedCertificate.FixedCertificateData

/-! ## §1.  The generic scaling bridge -/

/-- **`fcl_relative_error_of_scaling`.**  `KERNEL-PROVED`.

From the absolute scalings `B ≥ cB·X/log X` and `E ≤ cE·X/(log X)^{1+η}`, together with the
explicit threshold `cE ≤ δ·cB·(log X)^η`, the relative form `E ≤ δ·B` follows. -/
theorem fcl_relative_error_of_scaling
    {B E cB cE X delta eta : ℝ}
    (hX : 0 < X) (hL : 0 < Real.log X) (hcB : 0 < cB) (hdelta : 0 ≤ delta)
    (hB : cB * X / Real.log X ≤ B)
    (hE : E ≤ cE * X / (Real.log X) ^ (1 + eta))
    (hthr : cE ≤ delta * cB * (Real.log X) ^ eta) :
    E ≤ delta * B := by
  have hpow : (0 : ℝ) < (Real.log X) ^ eta := Real.rpow_pos_of_pos hL _
  have hsplit : (Real.log X) ^ (1 + eta) = Real.log X * (Real.log X) ^ eta := by
    rw [Real.rpow_add hL, Real.rpow_one]
  have hstep : cE * X / (Real.log X) ^ (1 + eta)
      ≤ delta * (cB * X / Real.log X) := by
    rw [hsplit]
    rw [div_le_iff₀ (by positivity)]
    have hXnn : (0 : ℝ) ≤ X := le_of_lt hX
    have h1 : cE * X ≤ delta * cB * (Real.log X) ^ eta * X :=
      mul_le_mul_of_nonneg_right hthr hXnn
    have h2 : delta * (cB * X / Real.log X) * (Real.log X * (Real.log X) ^ eta)
        = delta * cB * (Real.log X) ^ eta * X := by
      field_simp
    rw [h2]
    exact h1
  have hBmul : delta * (cB * X / Real.log X) ≤ delta * B :=
    mul_le_mul_of_nonneg_left hB hdelta
  linarith

/-- **`fcl_prime_mass_pos_of_scaling`.**  `CONDITIONAL_COMPILER / KERNEL-PROVED`.

The banked FCL positivity compiler, driven by the absolute analytic scalings through the
bridge above.  Every analytic statement is an explicit antecedent. -/
theorem fcl_prime_mass_pos_of_scaling
    (d : FixedCertificateData) (Cc E delta cB cE X eta : ℝ)
    (hX : 0 < X) (hL : 0 < Real.log X) (hcB : 0 < cB) (hdelta0 : 0 ≤ delta)
    (hLeak : LeakageBound d E)
    (hTotal : TotalCorrelationBound d E)
    (hMargin : ComparisonMargin d Cc E)
    (hB : cB * X / Real.log X ≤ d.B)
    (hE : E ≤ cE * X / (Real.log X) ^ (1 + eta))
    (hthr : cE ≤ delta * cB * (Real.log X) ^ eta)
    (hdelta : 3 * delta < 1 + Cc) :
    0 < ∑ p ∈ d.P, d.a p := by
  have hBpos : 0 < d.B := lt_of_lt_of_le (by positivity) hB
  exact fixedCertificate_prime_mass_pos d Cc E delta hLeak hTotal hMargin hBpos
    (fcl_relative_error_of_scaling hX hL hcB hdelta0 hB hE hthr) hdelta

/-! ## §2.  The threshold is a genuine hypothesis -/

/-- **`fcl_threshold_not_automatic`.**  `KERNEL-PROVED`.

The explicit threshold `cE ≤ δ·cB·(log X)^η` can fail, so the bridge is never available for
free: the "sufficiently large `X`" step is an antecedent, not a theorem. -/
theorem fcl_threshold_not_automatic :
    ∃ (cB cE X delta eta : ℝ),
      0 < cB ∧ 0 ≤ delta ∧ 0 < Real.log X ∧
        ¬ (cE ≤ delta * cB * (Real.log X) ^ eta) := by
  refine ⟨1, 1, Real.exp 1, 0, 0, one_pos, le_rfl, ?_, ?_⟩
  · rw [Real.log_exp]; exact one_pos
  · rw [Real.log_exp]
    simp

/-! ## §3.  The comparison-margin firewall -/

/-- **`PositiveMarginSupply`** — `SOURCE_OPEN / UNINHABITED`.

The conditional wrapper: it exposes *exactly* the source statement `0 < 1 + C_c`, and
nothing else.  No inhabitant is constructed. -/
structure PositiveMarginSupply (Cc : ℝ) : Prop where
  /-- The literal source positivity statement. -/
  margin : Erdos287.FordData.PositiveComparisonMargin Cc

/-- Conditional on a supplied positive margin, the canonical choice `δ = (1 + C_c)/6` is
admissible: it is nonnegative and satisfies the compiler's strict requirement. -/
theorem margin_delta_arithmetic {Cc : ℝ} (h : PositiveMarginSupply Cc) :
    0 ≤ (1 + Cc) / 6 ∧ 3 * ((1 + Cc) / 6) < 1 + Cc := by
  have hpos : 0 < 1 + Cc := h.margin
  constructor
  · linarith
  · linarith

/-- Conditional on a supplied positive margin and the analytic scalings at the canonical
`δ`, the certificate-positive region carries strictly positive prime mass. -/
theorem fcl_prime_mass_pos_of_margin
    (d : FixedCertificateData) (Cc E cB cE X eta : ℝ)
    (hmargin : PositiveMarginSupply Cc)
    (hX : 0 < X) (hL : 0 < Real.log X) (hcB : 0 < cB)
    (hLeak : LeakageBound d E)
    (hTotal : TotalCorrelationBound d E)
    (hMargin : ComparisonMargin d Cc E)
    (hB : cB * X / Real.log X ≤ d.B)
    (hE : E ≤ cE * X / (Real.log X) ^ (1 + eta))
    (hthr : cE ≤ (1 + Cc) / 6 * cB * (Real.log X) ^ eta) :
    0 < ∑ p ∈ d.P, d.a p := by
  obtain ⟨hd0, hd3⟩ := margin_delta_arithmetic hmargin
  exact fcl_prime_mass_pos_of_scaling d Cc E ((1 + Cc) / 6) cB cE X eta hX hL hcB hd0
    hLeak hTotal hMargin hB hE hthr hd3

/-- **`positiveMargin_not_automatic`.**  `KERNEL-PROVED`.  The margin wrapper is a genuine
source obligation. -/
theorem positiveMargin_not_automatic : ∃ Cc : ℝ, ¬ PositiveMarginSupply Cc := by
  refine ⟨-2, ?_⟩
  rintro ⟨h⟩
  rw [Erdos287.FordData.PositiveComparisonMargin] at h
  linarith

/-- **`certificatePinned_not_automatic`.**  `KERNEL-PROVED`.  The certificate pin is not
inhabited either: explicit data refute it. -/
theorem certificatePinned_not_automatic :
    ∃ (c2 : ℚ) (gSource : List ℚ → ℚ), ¬ Erdos287.FordData.CertificatePinned c2 gSource := by
  refine ⟨0, fun _ => 0, ?_⟩
  intro h
  have := h [] (by simp)
  rw [Erdos287.FordData.fordCandidate_empty] at this
  exact one_ne_zero this

/-! ## §4.  The `N2` separation -/

/-- **`fcl_N2_additive`.**  `KERNEL-PROVED`.

The `N2` slack is carried additively and nowhere else — this is exactly the banked
`fixedCertificate_leakage_compiler_N2`, restated so that the separation is visible. -/
theorem fcl_N2_additive (d : FixedCertificateData) (Cc E E₂ : ℝ)
    (hE₂ : 0 ≤ E₂)
    (hLeak : LeakageBound d E)
    (hTotal : TotalCorrelationBound d E)
    (hMargin : ComparisonMarginN2 d Cc E E₂) :
    PrimeMassLowerBound d ((1 + Cc) * d.B - 3 * E - 3 * E₂) :=
  fixedCertificate_leakage_compiler_N2 d Cc E E₂ hE₂ hLeak hTotal hMargin

/-- **`N2_slack_is_not_absorbed`.**  `KERNEL-PROVED`.

The `N2` term genuinely weakens the conclusion whenever it is positive: the `N2` bound is
strictly below the bound without it, so no silent absorption has taken place. -/
theorem N2_slack_is_not_absorbed {Cc B E E₂ : ℝ} (hE₂ : 0 < E₂) :
    (1 + Cc) * B - 3 * E - 3 * E₂ < (1 + Cc) * B - 3 * E := by linarith

end FCLBridge
end Erdos287
