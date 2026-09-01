import Mathlib
import RequestProject.Status.CurrentStatusErdos287SupersqrtFrontier
import RequestProject.CurrentProgramme.Erdos287FixedBudgetV22Arithmetic
import RequestProject.CurrentProgramme.Erdos287FixedDCutoffRepair
import RequestProject.CurrentProgramme.Erdos287FixedBudgetPhysicalWrapper
import RequestProject.CurrentProgramme.Erdos287AllAFirewall
import RequestProject.CurrentProgramme.Erdos287FCLAlgebraicBridge
import RequestProject.CurrentProgramme.Erdos287WindowPairExportEffectivity

/-!
# Authoritative status layer — fixed-budget V22 / FCL / effectivity

This append-only layer is later than every earlier status file.  It records:

```
STRONG ALL-A SUPERSQRT:              OPEN / NONCONTROLLING
FIXED-BUDGET V22 ARITHMETIC:         KERNEL-PROVED
FIXED-BUDGET PHYSICAL ANALYTIC INPUT:EXTERNAL / CONDITIONAL
CERTIFICATE POSITIVE MARGIN:         SOURCE OPEN unless supplied
FCL:                                 CONDITIONAL
WINDOWPAIR EXPORT:                   OPEN unless supplied
EFFECTIVITY:                         OPEN unless supplied
ERDOS287:                            OPEN
```

Each `kernelProved` row is tied to an actual theorem by a `backing_*` declaration, and each
open row is tied to a counterguard.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace FixedBudgetEffectivityStatus

open Erdos287.C0UnitaryFourierStatus
open Erdos287.FixedBudgetV22
open Erdos287.FixedDCutoff
open Erdos287.FixedBudgetPhysical
open Erdos287.AllAFirewall
open Erdos287.FCLBridge
open Erdos287.WindowPairExport
open Erdos287.V22Ledger
open Erdos287.V22Closure
open ResearchStatus

/-! ## §1  Nodes -/

/-- Rows of the fixed-budget / FCL / effectivity layer. -/
inductive BudgetNode
  /-- The strong all-`A` supersqrt statement. -/
  | strongAllASupersqrt
  /-- The fixed-budget V22 arithmetic at `B0 = 1`. -/
  | fixedBudgetArithmetic
  /-- The fixed-`D` cutoff repair. -/
  | fixedDCutoffRepair
  /-- The fixed-budget physical analytic input. -/
  | fixedBudgetPhysicalInput
  /-- The certificate positive comparison margin. -/
  | certificatePositiveMargin
  /-- The fixed-certificate leakage compiler route. -/
  | fcl
  /-- The window-pair export dictionary. -/
  | windowPairExport
  /-- Effectivity of the window-pair supply. -/
  | effectivity
  /-- Erdős problem #287 itself. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

open BudgetNode

/-- The authoritative ledger of this layer. -/
def budgetLedger : BudgetNode → ResearchStatus
  | strongAllASupersqrt => open_
  | fixedBudgetArithmetic => kernelProved
  | fixedDCutoffRepair => kernelProved
  | fixedBudgetPhysicalInput => conditionalSourcePin
  | certificatePositiveMargin => open_
  | fcl => conditionalSourcePin
  | windowPairExport => open_
  | effectivity => open_
  | erdos287 => open_

/-! ## §2  Ledger facts -/

theorem strongAllA_open : budgetLedger strongAllASupersqrt = open_ := rfl

theorem fixedBudgetArithmetic_kernelProved :
    budgetLedger fixedBudgetArithmetic = kernelProved := rfl

theorem windowPairExport_open : budgetLedger windowPairExport = open_ := rfl

theorem effectivity_open : budgetLedger effectivity = open_ := rfl

theorem erdos287_still_open : budgetLedger erdos287 = open_ := rfl

/-- No analytic row of this layer is recorded as kernel-proved. -/
theorem analytic_rows_not_kernelProved :
    budgetLedger strongAllASupersqrt ≠ kernelProved ∧
      budgetLedger fixedBudgetPhysicalInput ≠ kernelProved ∧
      budgetLedger certificatePositiveMargin ≠ kernelProved ∧
      budgetLedger fcl ≠ kernelProved ∧
      budgetLedger windowPairExport ≠ kernelProved ∧
      budgetLedger effectivity ≠ kernelProved ∧
      budgetLedger erdos287 ≠ kernelProved := by decide

/-! ## §3  Backing theorems -/

/-- Backing: the fixed-budget V22 arithmetic, exactly. -/
theorem backing_fixedBudget_arithmetic :
    cvar 1 = 5 ∧ 2 * CextStar < 5 ∧
      netLogExponent (cvar 1) CextStar = -5 / 4 ∧
      netLogExponent (cvar 1) CextStar < -1 :=
  ⟨cvar_one_eq_five, two_CextStar_lt_five,
    fixedBudget_B0_one_closes_at_cext_nine_fourths.2.1,
    fixedBudget_B0_one_closes_at_cext_nine_fourths.2.2⟩

/-- Backing: the budget is a choice, and `5/2` is the exact break-even point. -/
theorem backing_budget_sharpness :
    netLogExponent (cvar 1) (5 / 2) = -1 ∧ ¬ netLogExponent (cvar 1) (5 / 2) < -1 :=
  fixedBudget_fails_at_five_halves

/-- Backing: the fixed-`D` cutoff repair is a strict weakening of the banked interface. -/
theorem backing_fixedD_repair :
    (∀ (X Dana Dphys : ℝ) (unaccounted lowResidual : ℝ → ℝ),
        Erdos287.V21Cutoff.HighProjectorCutoffCompat3221 X 1 Dana Dphys unaccounted
            lowResidual →
          FixedDCutoffCompat3221 X Dana Dphys unaccounted lowResidual) ∧
      ∃ (X Dana Dphys : ℝ) (unaccounted lowResidual : ℝ → ℝ),
        FixedDCutoffCompat3221 X Dana Dphys unaccounted lowResidual ∧
          ¬ (∀ D' : ℝ, unaccounted D' = unaccounted Dana) :=
  ⟨fun _ _ _ _ _ h => fixedD_of_strong h, fixedD_does_not_give_all_D_invariance⟩

/-- Backing: the all-`A` firewall.  The strong all-`A` object implies the fixed-budget
input, and the converse fails, so the fixed-budget route is non-controlling for it. -/
theorem backing_allA_firewall :
    (∀ (E : ℝ → ℝ), ArbitraryLogCorrelationInput E → ∀ A : ℕ,
        ∃ Cerr : ℝ, FixedBudgetCorrelationInput E Cerr A) ∧
      ∃ (E : ℝ → ℝ) (Cerr : ℝ) (A : ℕ),
        FixedBudgetCorrelationInput E Cerr A ∧ ¬ ArbitraryLogCorrelationInput E :=
  allA_object_is_noncontrolling

/-- Backing: the FCL algebraic bridge and the explicitness of its threshold. -/
theorem backing_fcl_bridge :
    (∀ (B E cB cE X delta eta : ℝ), 0 < X → 0 < Real.log X → 0 < cB → 0 ≤ delta →
        cB * X / Real.log X ≤ B →
        E ≤ cE * X / (Real.log X) ^ (1 + eta) →
        cE ≤ delta * cB * (Real.log X) ^ eta → E ≤ delta * B) ∧
      ∃ (cB cE X delta eta : ℝ),
        0 < cB ∧ 0 ≤ delta ∧ 0 < Real.log X ∧
          ¬ (cE ≤ delta * cB * (Real.log X) ^ eta) :=
  ⟨fun _ _ _ _ _ _ _ hX hL hcB hd hB hE hthr =>
      fcl_relative_error_of_scaling hX hL hcB hd hB hE hthr,
    fcl_threshold_not_automatic⟩

/-- Backing: the comparison-margin arithmetic is available **only** conditionally, and the
margin itself is refutable. -/
theorem backing_margin_conditional :
    (∀ Cc : ℝ, PositiveMarginSupply Cc →
        0 ≤ (1 + Cc) / 6 ∧ 3 * ((1 + Cc) / 6) < 1 + Cc) ∧
      (∃ Cc : ℝ, ¬ PositiveMarginSupply Cc) ∧
      (∃ (c2 : ℚ) (gSource : List ℚ → ℚ),
        ¬ Erdos287.FordData.CertificatePinned c2 gSource) :=
  ⟨fun _ h => margin_delta_arithmetic h, positiveMargin_not_automatic,
    certificatePinned_not_automatic⟩

/-- Backing: the `N2` slack is additive and is not absorbed. -/
theorem backing_N2_separation :
    ∀ (Cc B E E₂ : ℝ), 0 < E₂ →
      (1 + Cc) * B - 3 * E - 3 * E₂ < (1 + Cc) * B - 3 * E :=
  fun _ _ _ _ h => N2_slack_is_not_absorbed h

/-- Backing: the window-pair export dictionary yields the literal supply, and is itself a
genuine obligation. -/
theorem backing_windowPair_export :
    (∀ (d : Erdos287.FixedCertificate.FixedCertificateData) (M x pu au pv av : ℕ),
        FixedCertificatePrimeMassToWindowPairInput d M x pu au pv av →
          WindowPairSupply M) ∧
      ∃ (d : Erdos287.FixedCertificate.FixedCertificateData) (M x pu au pv av : ℕ),
        ¬ FixedCertificatePrimeMassToWindowPairInput d M x pu au pv av :=
  ⟨fun _ _ _ _ _ _ _ h => windowPairSupply_of_export h, export_input_not_automatic⟩

/-- Backing: the effectivity firewall. -/
theorem backing_effectivity_firewall :
    ∃ p : ℕ → Prop, EventualSupply p ∧ ∀ s : EffectiveSupply p, ¬ s.Bounded :=
  eventual_does_not_give_bounded_effective

/-! ## §4  Scope guards -/

/-- The end-to-end adapter is conditional only: its premise is not constructed. -/
theorem guard_end_to_end_is_conditional :
    ∀ (s : EffectiveWindowPairSupply), s.Bounded → Erdos287Statement :=
  fun s h => erdos287Statement_of_boundedEffective s h

/-- The fixed-budget physical wrapper's budget field is a genuine restriction. -/
theorem guard_fixedBudgetPhysical_not_automatic : ∃ cext : ℚ, ¬ (2 * cext < 5) :=
  fixedBudgetPhysical_budget_not_automatic

/-- Nothing in this layer closes Erdős #287. -/
theorem guard_erdos287_open : budgetLedger erdos287 = open_ := rfl

end FixedBudgetEffectivityStatus
end Erdos287
