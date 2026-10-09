import Mathlib
import RequestProject.Erdos287.CurrentStatusEffectivity
import RequestProject.Erdos287.CompletePeriodEndpoint
import RequestProject.Erdos287.LambdaWeights
import RequestProject.Erdos287.EdgeCutoffLedger
import RequestProject.Erdos287.AggregateThreshold
import RequestProject.Erdos287.AllQResummation
import RequestProject.Erdos287.ChartEquivalence

/-!
# Erdős #287 effectivity — current status after the long-fibre run (§30)

This file **extends** `CurrentStatusEffectivity`; the §22/§23 status ledger there is
preserved unchanged.  The long-fibre additions are:

```
V<1000 EDGE:                          CLOSED / CERTIFIED INPUT
CERTIFIED SUBTOTAL:                   5.257263872e-7
REMAINING CAPACITY:                   3.603386128e-7
COMPLETE-PERIOD ENDPOINT IDENTITY:    KERNEL-PROVED
COMPLETE-PERIOD ENDPOINT NUM. UPPER:  CERTIFICATE / CONDITIONAL
LAMBDA FINITE ALGEBRA:                KERNEL-PROVED
EDGE REPLACEMENT SEMANTICS:           KERNEL-PROVED
AGGREGATE THRESHOLD ARITHMETIC:       KERNEL-PROVED
REMAINING COVARIANCE TARGET:          C_F + 2 C_ED + C_DD + C_S < 283/37500.  OPEN
ALL-q RESUMMATION:                    ALGEBRA KERNEL-PROVED
SMOOTH SINGULAR-SERIES DISCREPANCY:   OPEN
CHART EQUIVALENCE:                    KERNEL-PROVED (source typing)
UNWEIGHTED PER-b C_joint ≤ 0.09:      RETIRED / NOT BANKED
MEDIUM-k:                             STRICTLY REDUCED / OPEN
TWO-HIGH:                             NOT ENTERED
SIGNED FLOOR:                         OPEN
MAYNARD:                              NOT ENTERED
ERDŐS #287:                           OPEN
```

The λ-weighted aggregate covariance bound, the achieved estimate `C_agg ≤ 69/5000`, the
finite-period remainder estimate, the endpoint-derivative and derivative-derivative
estimates, the singular-series discrepancy theorem, the medium-`k` and two-high closures,
the signed-floor closure, Maynard and Erdős #287 itself are **not** proved anywhere in this
package; `longFibre_open_frontier` records each of them as unproved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Effectivity

/-! ## §30.1  The long-fibre status ledger -/

/-- The nodes tracked after the long-fibre run. -/
inductive LongFibreNode
  | v1000Edge
  | certifiedSubtotal
  | remainingCapacity
  | completePeriodEndpointIdentity
  | completePeriodEndpointNumericalUpper
  | lambdaFiniteAlgebra
  | edgeReplacementSemantics
  | aggregateThresholdArithmetic
  | remainingCovarianceTarget
  | allQResummation
  | smoothSingularSeriesDiscrepancy
  | chartEquivalence
  | unweightedPerBCjoint009
  | mediumK
  | twoHigh
  | signedFloor
  | maynard
  | erdos287
  deriving DecidableEq, Repr

/-- The status values used by the long-fibre ledger. -/
inductive LongFibreStatus
  | kernelProved
  | certifiedInput
  | conditionalCertificate
  | strictlyReducedOpen
  | retired
  | openNode
  | notEntered
  deriving DecidableEq, Repr

/-- The status of each tracked node. -/
def longFibreStatus : LongFibreNode → LongFibreStatus
  | .v1000Edge => .certifiedInput
  | .certifiedSubtotal => .kernelProved
  | .remainingCapacity => .kernelProved
  | .completePeriodEndpointIdentity => .kernelProved
  | .completePeriodEndpointNumericalUpper => .conditionalCertificate
  | .lambdaFiniteAlgebra => .kernelProved
  | .edgeReplacementSemantics => .kernelProved
  | .aggregateThresholdArithmetic => .kernelProved
  | .remainingCovarianceTarget => .openNode
  | .allQResummation => .kernelProved
  | .smoothSingularSeriesDiscrepancy => .openNode
  | .chartEquivalence => .kernelProved
  | .unweightedPerBCjoint009 => .retired
  | .mediumK => .strictlyReducedOpen
  | .twoHigh => .notEntered
  | .signedFloor => .openNode
  | .maynard => .notEntered
  | .erdos287 => .openNode

/-- The nodes that must remain unproved after this run. -/
def longFibreOpenNodes : List LongFibreNode :=
  [.remainingCovarianceTarget, .smoothSingularSeriesDiscrepancy, .mediumK, .twoHigh,
   .signedFloor, .maynard, .erdos287, .unweightedPerBCjoint009]

/-- **`longFibre_open_frontier`.**  `KERNEL-PROVED`.  No node of the open frontier — the
remaining covariance target, the smooth singular-series discrepancy, medium-`k`, two-high,
the signed floor, Maynard, Erdős #287, and the retired unweighted `C_joint` estimate — is
recorded as kernel-proved, as a certified input, or as a conditional certificate. -/
theorem longFibre_open_frontier :
    ∀ n ∈ longFibreOpenNodes,
      longFibreStatus n ≠ LongFibreStatus.kernelProved ∧
        longFibreStatus n ≠ LongFibreStatus.certifiedInput ∧
        longFibreStatus n ≠ LongFibreStatus.conditionalCertificate := by decide

/-- **`erdos287_still_open`.**  `KERNEL-PROVED`.  Erdős #287 is recorded as open. -/
theorem erdos287_still_open : longFibreStatus .erdos287 = LongFibreStatus.openNode := rfl

/-- **`mediumK_reduced_not_closed`.**  `KERNEL-PROVED`.  Medium-`k` is strictly reduced but
not closed. -/
theorem mediumK_reduced_not_closed :
    longFibreStatus .mediumK = LongFibreStatus.strictlyReducedOpen ∧
      longFibreStatus .mediumK ≠ LongFibreStatus.kernelProved := ⟨rfl, by decide⟩

/-- **`twoHigh_and_maynard_not_entered`.**  `KERNEL-PROVED`. -/
theorem twoHigh_and_maynard_not_entered :
    longFibreStatus .twoHigh = LongFibreStatus.notEntered ∧
      longFibreStatus .maynard = LongFibreStatus.notEntered := ⟨rfl, rfl⟩

/-- **`v1000_edge_certified_input`.**  `KERNEL-PROVED`.  The `V<1000` edge enters the ledger
as a certified *input*, never as a kernel-proved analytic estimate. -/
theorem v1000_edge_certified_input :
    longFibreStatus .v1000Edge = LongFibreStatus.certifiedInput ∧
      longFibreStatus .v1000Edge ≠ LongFibreStatus.kernelProved := ⟨rfl, by decide⟩

/-- **`longFibre_ledger_values`.**  `KERNEL-PROVED`.  The printed ledger values are the
banked exact rationals, and the target/subtotal/capacity arithmetic closes. -/
theorem longFibre_ledger_values :
    certifiedSubtotalV1000 = 5257263872 / 10 ^ 16 ∧
      remainingCapacityV1000 = 3603386128 / 10 ^ 16 ∧
      ledgerTarget - certifiedSubtotalV1000 = remainingCapacityV1000 :=
  ⟨rfl, rfl, ledger_difference_exact_v1000⟩

/-! ## §30.2  Axiom audit for the long-fibre additions -/

section AxiomAudit

-- §24 complete-period endpoint covariance
#print axioms sum_range_mod_mul_mod
#print axioms sum_range_shift
#print axioms endpointPhi_sum_period
#print axioms endpointCovariance_exact
#print axioms endpointCovariance_coprime_zero
#print axioms endpointCovariance_nonneg
#print axioms endpointCovariance_gcd_stratum
#print axioms endpointCovariance_lane_independent
#print axioms endpointCovariance_odd
#print axioms endpointCovariance_pos_of_gcd_gt_one

-- §25 λ finite algebra
#print axioms lambdaW_mul
#print axioms lambdaW_pos
#print axioms lambdaW_prod_primes
#print axioms lambdaLocal_eq
#print axioms lambdaW_eq_B0_mul_beta
#print axioms HlambdaFinite_split
#print axioms HlambdaFinite_pos
#print axioms Hlambda_conditional_bound
#print axioms Hlambda_not_asserted

-- §26 the V<1000 edge replacement and the new ledger
#print axioms ledger_difference_exact_v1000
#print axioms remaining_capacity_v1000_gt
#print axioms ledgerV1000_supersedes
#print axioms updatedSubtotal_eq
#print axioms edge_double_charge_illegal
#print axioms subtotal_update_v1000
#print axioms certifiedSubtotalV1000_eq
#print axioms edgeCertificate_v1000
#print axioms edgeCertificate_not_proved

-- §27 aggregate threshold arithmetic and the remainder ledger
#print axioms CAggTarget_lt_critical
#print axioms CAgg_below_critical_of_target
#print axioms CAggBound_not_proved
#print axioms aggregate_minus_endpoint
#print axioms endpoint_budget_positive
#print axioms diag_off_not_period
#print axioms CRem_eq
#print axioms CRem_le_of_components
#print axioms remaining_target_not_proved
#print axioms aggregate_closure_conditional

-- §28 the exact all-q resummation
#print axioms B0_pos
#print axioms allQ_divisor_identity
#print axioms AgtDivisorSum_eq
#print axioms allQ_resummation
#print axioms allQ_discrepancy_form

-- §29 chart equivalence and retired-theorem firewalls
#print axioms charts_same_source
#print axioms chart_double_charge_illegal
#print axioms chartLegal_single_chart
#print axioms chartLegal_singleton
#print axioms unweightedCjoint_retired
#print axioms unweightedCjoint_not_banked
#print axioms bankedClosingEstimates_are_banked

-- §30 status
#print axioms longFibre_open_frontier
#print axioms longFibre_ledger_values
#print axioms erdos287_still_open

end AxiomAudit

end Effectivity
end Erdos287
