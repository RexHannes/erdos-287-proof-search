import Mathlib
import RequestProject.Erdos287.BsrcWeights
import RequestProject.Erdos287.AllComplement
import RequestProject.Erdos287.OddHalfDivisor
import RequestProject.Erdos287.Reflection
import RequestProject.Erdos287.MediumLedger
import RequestProject.Erdos287.C1C2Splice
import RequestProject.Erdos287.OddLineCancellation
import RequestProject.Erdos287.RatioBoundary
import RequestProject.Erdos287.EulerLocal
import RequestProject.Erdos287.TwoVariableZ
import RequestProject.Erdos287.PerronAlgebra
import RequestProject.Erdos287.IncrementalDirectedLedger
import RequestProject.Erdos287.ProblemStatement

/-!
# Erdős #287 effectivity — current status ledger and open-frontier firewall (§22, §23)

```
PHYSICAL B1 NORMALIZATION:          KERNEL-PROVED
ALL-COMPLEMENT DISCRETE:            KERNEL-PROVED
CONTINUOUS EULER IDENTITY:          KERNEL-PROVED (finite) / CONDITIONAL (infinite)
ODD HALF-DIVISOR:                   KERNEL-PROVED
w = 6 FIREWALL:                     KERNEL-PROVED
FULL-vs-MEDIUM TYPING:              KERNEL-PROVED
INCREMENTAL LEDGER TYPE:            KERNEL-PROVED
HALF-DIVISOR REFLECTION:            KERNEL-PROVED
c1/c2 DISCRETE SPLICE:              KERNEL-PROVED
c1/c2 CONTINUOUS SPLICE:            KERNEL-PROVED (integrability hypothesis)
FULL ODD DISCRETE CANCELLATION:     KERNEL-PROVED
CONTINUOUS COEFFICIENT CONVOLUTION: KERNEL-PROVED
RATIO-BOUNDARY:                     KERNEL-PROVED (conditional)
G_p LOCAL FACTOR:                   KERNEL-PROVED
FINITE B1·G(u,0) = 1:               KERNEL-PROVED
TWO-VARIABLE LOCAL EULER IDENTITY:  KERNEL-PROVED
FINITE Z(s,s) = 0:                  KERNEL-PROVED
INFINITE Z(s,s) = 0:                BLOCKED BY ANALYTIC CONVERGENCE
G ABSOLUTE-CONVERGENCE REGION:      PARTIAL (v = 0 slice only)
PERRON VARIABLE CHANGE:             KERNEL-PROVED (algebra only)
STRICT EQUALITY ALGEBRA:            KERNEL-PROVED (conditional)
INCREMENTAL LEDGER ARITHMETIC:      KERNEL-PROVED
JOINED SQUARE FUNCTION:             OPEN
MEDIUM-k:                           OPEN
TWO-HIGH GAP:                       OPEN / NOT ENTERED
SIGNED FLOOR:                       OPEN
MAYNARD:                            NOT ENTERED (no predicate exists in this package)
ERDŐS #287:                         OPEN
```

## Open-frontier firewall (§22)

The nodes below are left **unproved and uninhabited**.  `Erdos287Solved` is the honest
statement of the problem and is *not* proved anywhere in this package; `frontierStatus`
records every listed node as `open`, and `erdos287_not_claimed` witnesses that this file
asserts nothing about it.  No Maynard-type predicate is introduced at all.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Finset

namespace Erdos287
namespace Effectivity

/-! ## §22  Open frontier -/

/-- The joined square-function bound with constant `C` for a supplied family of square
function values `S` and weights `w`.  **Not proved for any physical family.** -/
def JoinedSquareFunctionBound (C : ℝ) (S w : ℕ → ℝ) (F : Finset ℕ) : Prop :=
  ∑ n ∈ F, (S n) ^ 2 ≤ C * ∑ n ∈ F, w n

/-- `C_joint ≤ 0.09` for a supplied constant.  The physical `C_joint` is **not defined**
in this package, so nothing instantiates this predicate. -/
def JointConstantBound (Cjoint : ℝ) : Prop := Cjoint ≤ 9 / 100

/-- The medium-`k` closure for a supplied residual and budget.  **Open.** -/
def MediumKClosed (residual budget : ℝ) : Prop := |residual| ≤ budget

/-- The two-high gap closure for a supplied residual and budget.  **Open / not entered.** -/
def TwoHighGapClosed (residual budget : ℝ) : Prop := |residual| ≤ budget

/-- The signed-floor closure for a supplied floor and target.  **Open.** -/
def SignedFloorClosed (floorValue target : ℝ) : Prop := target ≤ floorValue

/-- **The honest statement of Erdős #287.**  It is *not* proved here. -/
def Erdos287Solved : Prop := ∀ A : Finset ℕ, ¬ Erdos287Counterexample A

/-- The nodes of the open frontier. -/
inductive FrontierNode
  | joinedSquareFunction
  | jointConstant
  | mediumK
  | twoHighGap
  | signedFloor
  | erdos287
  deriving DecidableEq, Repr

/-- Node status. -/
inductive NodeStatus
  | kernelProved
  | conditional
  | openNode
  deriving DecidableEq, Repr

/-- Every frontier node is `open`. -/
def frontierStatus : FrontierNode → NodeStatus := fun _ => NodeStatus.openNode

/-- **`frontier_all_open`.**  `KERNEL-PROVED`.  No node of the open frontier is recorded as
proved or as conditional. -/
theorem frontier_all_open (n : FrontierNode) : frontierStatus n = NodeStatus.openNode := rfl

/-- **`erdos287_not_claimed`.**  `KERNEL-PROVED`.  This package makes no claim about
Erdős #287: the statement is recorded, and the only theorem about it here is that it is
equivalent to itself. -/
theorem erdos287_not_claimed : Erdos287Solved ↔ ∀ A : Finset ℕ, ¬ Erdos287Counterexample A :=
  Iff.rfl

/-! ## §23  Axiom audit -/

section AxiomAudit

open Erdos287.Effectivity

-- §2 physical `B_src` normalisation
#print axioms B0_mul
#print axioms beta_mul
#print axioms B_mul_typed
#print axioms B1_onceFirewall

-- §3 all-complement discrete identity
#print axioms sum_divisors_of_squarefreeSupported
#print axioms allComplement_discrete
#print axioms allComplement_discrete_odd

-- §5, §6 odd half-divisor chart
#print axioms halfDivisor_variable_change
#print axioms Hodd_one_six
#print axioms Hall_one_six
#print axioms w6_firewall

-- §7, §8 full-vs-medium typing and the ledger firewall
#print axioms mediumChart_ne_fullChart
#print axioms simpleCoefficient_not_medium
#print axioms incrementalLedger_retains
#print axioms incrementalLedger_rejects_full
#print axioms no_naive_full_insertion
#print axioms fullReplacement_requires_removal

-- §9 half-divisor reflection
#print axioms halfDivisor_reflection_strict
#print axioms halfDivisor_reflection_nonstrict
#print axioms radOdd_one_source_vanishes
#print axioms halfDivisor_vanishes_of_moebius_one

-- §10, §11 the `c = 1 / c = 2` splice
#print axioms discrete_splice
#print axioms continuous_splice_pointwise
#print axioms continuous_splice

-- §12, §13 the odd line cancellations
#print axioms oddLine_coefficient_zero
#print axioms oddLine_Wsum_zero
#print axioms muOddOverPhi_eq_mOdd_conv_r
#print axioms downstream_cancellation_of_sum_mOdd_zero

-- §14 ratio-boundary form
#print axioms ratio_boundary_form

-- §4, §15, §16, §18 Euler local factors
#print axioms euler_local_identity
#print axioms betaOverK_finite_sum
#print axioms continuousEuler_conditional
#print axioms localRatio_closed_form
#print axioms localNumerator_vanishes_at_zero
#print axioms twoFactor_zero
#print axioms twoFactor_zero_ne_zero
#print axioms Gloc_at_v_zero
#print axioms B1fin_mul_Gfin_v_zero
#print axioms Gloc_v_zero_majorant

-- §17 two-variable Euler identity
#print axioms eulerNum_split
#print axioms eulerNum_diag
#print axioms finite_Z_diag_zero
#print axioms Gloc_diag

-- §19, §20 Perron algebra
#print axioms perron_change_of_variables
#print axioms perronJacobian_det
#print axioms perronJacobianInv_abs_det
#print axioms perron_kernel_compensation
#print axioms strict_perron_outer_factor

-- §21 incremental directed ledger
#print axioms ledger_difference_exact
#print axioms remaining_capacity_gt
#print axioms auditedLedger_retains

-- §22 open frontier
#print axioms frontier_all_open
#print axioms erdos287_not_claimed

end AxiomAudit

end Effectivity
end Erdos287
