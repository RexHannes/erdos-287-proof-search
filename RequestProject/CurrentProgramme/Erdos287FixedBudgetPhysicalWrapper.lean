import Mathlib
import RequestProject.Erdos287.TwoProjectorPhysicalClosure3221
import RequestProject.CurrentProgramme.Erdos287FixedBudgetV22Arithmetic
import RequestProject.CurrentProgramme.Erdos287FixedDCutoffRepair

/-!
# The fixed-budget physical wrapper at `B0 = 1`

`FIXED-BUDGET PHYSICAL ANALYTIC INPUT : EXTERNAL / CONDITIONAL`

`Erdos287.V22Closure.TwoProjectorPhysical3221Inputs` is **preserved unchanged**.  This file
appends the fixed-budget wrapper, which differs from it in exactly two places:

* the cutoff field is the *source-exact* fixed-`D` interface at `B0 = 1`
  (`FixedDCutoffCompat3221`), not the stronger all-`D` interface;
* the ledger field is the *explicit numeric budget* `2·Cext < 5`, matching `Cvar(1) = 5`.

Every remaining field is literally the corresponding external source interface of the
banked physical package.  **No analytic field is inhabited, and no `axiom` is introduced.**
The wrapper is therefore uninhabited here; only the conditional implication is proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace FixedBudgetPhysical

open Erdos287.V22Ledger
open Erdos287.V22Closure
open Erdos287.V21PrimeBox
open Erdos287.V21Sieve
open Erdos287.V21Shiu
open Erdos287.V21Cutoff
open Erdos287.V21Outer
open Erdos287.V22Ford
open Erdos287.V22PrimeBoxL1
open Erdos287.HighCond3221
open Erdos287.V21Compiler
open Erdos287.FixedBudgetV22
open Erdos287.FixedDCutoff

/-! ## §1.  The wrapper -/

/-- **`FixedBudgetTwoProjectorPhysical3221Inputs`** — `EXTERNAL / CONDITIONAL / UNINHABITED`.

The physical two-projector source at the fixed cutoff exponent `B0 = 1`, together with an
explicit rational log-prefactor budget `Cext` satisfying `2·Cext < 5 = Cvar(1)`. -/
structure FixedBudgetTwoProjectorPhysical3221Inputs
    (Dat : InverseSampledHighCond3221Data)
    (F : Ford723CoefficientData) (Pdat : PrimeBoxData) (C1 Y : ℝ)
    (Sdat : ShortShiftSieveData)
    (Wprime : ℕ) (s : ℤ) (Mbox : Finset ℕ) (M X Cshiu : ℝ)
    (P1 P2 MboxOuter : Finset ℕ) (w1 w2 : ℕ → ℂ) (Couter : ℝ)
    (Dana Dphys : ℝ) (unaccounted lowResidual : ℝ → ℝ)
    (cext : ℚ)
    (naturalScale Lsave vAA vBA vAB vBB : ℝ) : Prop where
  /-- The source dictionary for the physical `ω_i` (SOURCE_OPEN). -/
  dictionary : BalancedSevenOmegaFord723Adapter3221 F Pdat
  /-- The prime-box cardinality input (external prime counting). -/
  primeCount : PrimeBoxCardinality3221Input Pdat C1 Y
  /-- The external short-shift rough sieve input. -/
  sieve : ShortShiftRoughSieve3221Input Sdat
  /-- The external Shiu divisor-average input. -/
  shiu : ShiuLinearDivisorAverage3221Input Wprime s Mbox M X Cshiu
  /-- The outer two-prime `L²` input. -/
  outerL2 : OuterTwoPrimeL2Normalization3221Input P1 P2 MboxOuter w1 w2 M X Couter
  /-- The **fixed**-cutoff compatibility interface at `D = log X`. -/
  cutoff : FixedDCutoffCompat3221 X Dana Dphys unaccounted lowResidual
  /-- The explicit fixed budget against the ledger value `Cvar(1) = 5`. -/
  budget : 2 * cext < 5
  /-- The numeric budget layer transporting the ledger to the four channels. -/
  numeric : TwoHighProjector3221ClosureInputs Dat naturalScale Lsave vAA vBA vAB vBB

/-! ## §2.  The conditional compiler -/

/-- **`fixedBudgetPhysical_closes_logVar`.**  `CONDITIONAL_COMPILER / KERNEL-PROVED`.

The fixed-budget wrapper yields the log-variance interface together with the strict closure
inequality `netLogExponent(Cvar(1), Cext) < −1`.  There is no inhabitant of the wrapper. -/
theorem fixedBudgetPhysical_closes_logVar
    {Dat : InverseSampledHighCond3221Data}
    {F : Ford723CoefficientData} {Pdat : PrimeBoxData} {C1 Y : ℝ}
    {Sdat : ShortShiftSieveData}
    {Wprime : ℕ} {s : ℤ} {Mbox : Finset ℕ} {M X Cshiu : ℝ}
    {P1 P2 MboxOuter : Finset ℕ} {w1 w2 : ℕ → ℂ} {Couter : ℝ}
    {Dana Dphys : ℝ} {unaccounted lowResidual : ℝ → ℝ}
    {cext : ℚ}
    {naturalScale Lsave vAA vBA vAB vBB : ℝ}
    (h : FixedBudgetTwoProjectorPhysical3221Inputs Dat F Pdat C1 Y Sdat Wprime s Mbox M X
      Cshiu P1 P2 MboxOuter w1 w2 Couter Dana Dphys unaccounted lowResidual cext
      naturalScale Lsave vAA vBA vAB vBB) :
    InverseSampledHighCondLogVar3221Input Dat naturalScale Lsave ∧
      netLogExponent (cvar 1) cext < -1 :=
  ⟨twoHighProjector3221_closes_logVar h.numeric,
    fixedBudget_closes_of_two_cext_lt_five h.budget⟩

/-- At the distinguished budget `Cext = 9/4` the wrapper gives the exact value `−5/4`. -/
theorem fixedBudgetPhysical_netExponent_at_CextStar
    {Dat : InverseSampledHighCond3221Data}
    {F : Ford723CoefficientData} {Pdat : PrimeBoxData} {C1 Y : ℝ}
    {Sdat : ShortShiftSieveData}
    {Wprime : ℕ} {s : ℤ} {Mbox : Finset ℕ} {M X Cshiu : ℝ}
    {P1 P2 MboxOuter : Finset ℕ} {w1 w2 : ℕ → ℂ} {Couter : ℝ}
    {Dana Dphys : ℝ} {unaccounted lowResidual : ℝ → ℝ}
    {naturalScale Lsave vAA vBA vAB vBB : ℝ}
    (_h : FixedBudgetTwoProjectorPhysical3221Inputs Dat F Pdat C1 Y Sdat Wprime s Mbox M X
      Cshiu P1 P2 MboxOuter w1 w2 Couter Dana Dphys unaccounted lowResidual CextStar
      naturalScale Lsave vAA vBA vAB vBB) :
    netLogExponent (cvar 1) CextStar = -5 / 4 :=
  fixedBudget_B0_one_closes_at_cext_nine_fourths.2.1

/-! ## §3.  Adapters and firewalls -/

/-- **`twoProjectorPhysical_of_fixedBudget_and_strongCutoff`.**  `KERNEL-PROVED`.

The wrapper is exactly the banked physical package with the cutoff field weakened: adding
back the stronger all-`D` cutoff interface at `B0 = 1` recovers the banked structure. -/
theorem twoProjectorPhysical_of_fixedBudget_and_strongCutoff
    {Dat : InverseSampledHighCond3221Data}
    {F : Ford723CoefficientData} {Pdat : PrimeBoxData} {C1 Y : ℝ}
    {Sdat : ShortShiftSieveData}
    {Wprime : ℕ} {s : ℤ} {Mbox : Finset ℕ} {M X Cshiu : ℝ}
    {P1 P2 MboxOuter : Finset ℕ} {w1 w2 : ℕ → ℂ} {Couter : ℝ}
    {Dana Dphys : ℝ} {unaccounted lowResidual : ℝ → ℝ}
    {cext : ℚ}
    {naturalScale Lsave vAA vBA vAB vBB : ℝ}
    (h : FixedBudgetTwoProjectorPhysical3221Inputs Dat F Pdat C1 Y Sdat Wprime s Mbox M X
      Cshiu P1 P2 MboxOuter w1 w2 Couter Dana Dphys unaccounted lowResidual cext
      naturalScale Lsave vAA vBA vAB vBB)
    (hstrong : HighProjectorCutoffCompat3221 X 1 Dana Dphys unaccounted lowResidual) :
    TwoProjectorPhysical3221Inputs Dat F Pdat C1 Y Sdat Wprime s Mbox M X Cshiu
      P1 P2 MboxOuter w1 w2 Couter 1 Dana Dphys unaccounted lowResidual cext
      naturalScale Lsave vAA vBA vAB vBB where
  dictionary := h.dictionary
  primeCount := h.primeCount
  sieve := h.sieve
  shiu := h.shiu
  outerL2 := h.outerL2
  cutoff := hstrong
  ledger := by rw [cvar_one_eq_five]; exact h.budget
  budget := h.numeric

/-- **`fixedBudgetPhysical_budget_not_automatic`.**  `KERNEL-PROVED`.

The budget field is a genuine restriction: it fails for explicit rational budgets, so the
wrapper cannot be manufactured. -/
theorem fixedBudgetPhysical_budget_not_automatic : ∃ cext : ℚ, ¬ (2 * cext < 5) :=
  ⟨3, by norm_num⟩

end FixedBudgetPhysical
end Erdos287
