import Mathlib
import RequestProject.Erdos287.CurrentStatusEffectivityLongFibre
import RequestProject.Erdos287.ProperGammaQFibre
import RequestProject.Erdos287.ProperGammaLaneRecombination
import RequestProject.Erdos287.ProperGammaSource
import RequestProject.Erdos287.ProperGammaMultiplicityGeometry
import RequestProject.Erdos287.ProperGammaShellSix
import RequestProject.Erdos287.ProperGammaCurrentSurvivor
import RequestProject.Erdos287.ProperGammaProductResummation
import RequestProject.Erdos287.ProperGammaOddConvolution
import RequestProject.Erdos287.ProperGammaTruncatedDivisor
import RequestProject.Erdos287.ProperGammaMultiplicityLedger

/-!
# Erdős #287 effectivity — status after the proper-γ multiplicity run (§41)

This file **extends** `CurrentStatusEffectivity` and `CurrentStatusEffectivityLongFibre`; the
long-fibre bank is preserved unchanged and remains trusted at its declared scope, but it is no
longer the live frontier coordinate.

```
LONG-FIBRE:                       HISTORICAL / BANKED
H transition family:              CLOSED AT DECLARED CERTIFICATE SCOPE
P transition family:              CLOSED AT DECLARED CERTIFICATE SCOPE
gamma self-modulus ell = d:       CLOSED AT DECLARED CERTIFICATE SCOPE
proper gamma q ≤ 200:             CLOSED AT DECLARED CERTIFICATE SCOPE
proper gamma N = 1:               CLOSED AT DECLARED CERTIFICATE SCOPE
proper gamma N = 2..5:            CLOSED AT DECLARED CERTIFICATE SCOPE
proper gamma N = 6:               CLOSED AT DECLARED CERTIFICATE SCOPE
proper gamma N ≥ 7:               OPEN
proper gamma (ell > d):           STRICTLY REDUCED / OPEN
S_live:                           OPEN
R_012:                            OPEN
signed floor:                     OPEN
Maynard:                          NOT ENTERED
final splice:                     OPEN
ERDŐS #287:                       OPEN
```

The evidence taxonomy distinguishes `KERNEL_PROVED`, `CERTIFICATE_BACKED`,
`CONDITIONAL_ANALYTIC`, `RETIRED_NONCLOSING_METHOD`, `OPEN` and `NOT_ENTERED`; the theorem
`properGammaMultiplicity_open_frontier` proves that no open node is tagged as closed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Effectivity

/-! ## §41.1  The evidence taxonomy -/

/-- The evidence classes used by the proper-γ multiplicity bank. -/
inductive Evidence
  | kernelProved
  | certificateBacked
  | conditionalAnalytic
  | retiredNonclosingMethod
  | openNode
  | notEntered
  deriving DecidableEq, Repr

/-- Evidence classes that count as *closed* for bookkeeping purposes. -/
def Evidence.isClosed : Evidence → Bool
  | .kernelProved => true
  | .certificateBacked => true
  | .conditionalAnalytic => false
  | .retiredNonclosingMethod => false
  | .openNode => false
  | .notEntered => false

/-! ## §41.2  The tracked nodes -/

/-- The nodes tracked after the proper-γ multiplicity run. -/
inductive MultiplicityNode
  | longFibreBank
  | hTransitionFamily
  | pTransitionFamily
  | gammaSelfModulus
  | qFibreAlgebra
  | laneRecombination
  | properGammaSourceDefinition
  | multiplicityBandGeometry
  | productChangeOfVariables
  | lowerCutoffFirewall
  | truncatedDivisorIdentity
  | oddConvolutionAlgebra
  | factorTwoErrorAlgebra
  | ownershipArithmetic
  | parentChildNoDoubleCharge
  | shellSixGeometry
  | properGammaQ200Closure
  | properGammaN1Closure
  | properGammaN2to5Closure
  | properGammaN6Closure
  | eulerProductConstants
  | oddSeriesIdentity
  | absoluteVariationTail
  | weightedKsRecurrence
  | identityFactoryLanding
  | closingPrefixBound
  | properGammaNge7
  | properGammaNge6Parent
  | properGammaFullClosure
  | sLive
  | r012
  | signedFloor
  | maynard
  | finalSplice
  | erdos287
  deriving DecidableEq, Repr

/-- The evidence class of each tracked node. -/
def multiplicityEvidence : MultiplicityNode → Evidence
  | .longFibreBank => .certificateBacked
  | .hTransitionFamily => .certificateBacked
  | .pTransitionFamily => .certificateBacked
  | .gammaSelfModulus => .certificateBacked
  | .qFibreAlgebra => .kernelProved
  | .laneRecombination => .kernelProved
  | .properGammaSourceDefinition => .kernelProved
  | .multiplicityBandGeometry => .kernelProved
  | .productChangeOfVariables => .kernelProved
  | .lowerCutoffFirewall => .kernelProved
  | .truncatedDivisorIdentity => .kernelProved
  | .oddConvolutionAlgebra => .kernelProved
  | .factorTwoErrorAlgebra => .kernelProved
  | .ownershipArithmetic => .kernelProved
  | .parentChildNoDoubleCharge => .kernelProved
  | .shellSixGeometry => .kernelProved
  | .properGammaQ200Closure => .certificateBacked
  | .properGammaN1Closure => .certificateBacked
  | .properGammaN2to5Closure => .certificateBacked
  | .properGammaN6Closure => .certificateBacked
  | .eulerProductConstants => .certificateBacked
  | .oddSeriesIdentity => .conditionalAnalytic
  | .absoluteVariationTail => .retiredNonclosingMethod
  | .weightedKsRecurrence => .openNode
  | .identityFactoryLanding => .conditionalAnalytic
  | .closingPrefixBound => .openNode
  | .properGammaNge7 => .openNode
  | .properGammaNge6Parent => .openNode
  | .properGammaFullClosure => .openNode
  | .sLive => .openNode
  | .r012 => .openNode
  | .signedFloor => .openNode
  | .maynard => .notEntered
  | .finalSplice => .openNode
  | .erdos287 => .openNode

/-- The nodes that must remain unclosed after this run. -/
def multiplicityOpenNodes : List MultiplicityNode :=
  [.properGammaNge7, .properGammaNge6Parent, .properGammaFullClosure, .sLive, .r012,
   .signedFloor, .maynard, .finalSplice, .erdos287, .weightedKsRecurrence,
   .closingPrefixBound, .absoluteVariationTail, .oddSeriesIdentity, .identityFactoryLanding]

/-- **`properGammaMultiplicity_open_frontier`.**  `KERNEL-PROVED`.  No node of the open
frontier is tagged `kernelProved` or `certificateBacked`; in particular none is closed. -/
theorem properGammaMultiplicity_open_frontier :
    ∀ n ∈ multiplicityOpenNodes,
      multiplicityEvidence n ≠ Evidence.kernelProved ∧
        multiplicityEvidence n ≠ Evidence.certificateBacked ∧
        (multiplicityEvidence n).isClosed = false := by decide

/-- **`erdos287_open_multiplicity`.**  `KERNEL-PROVED`.  Erdős #287 remains open. -/
theorem erdos287_open_multiplicity :
    multiplicityEvidence .erdos287 = Evidence.openNode := rfl

/-- **`survivor_Nge7_open`.**  `KERNEL-PROVED`.  The current survivor `N ≥ 7` is open, and so
is the recombined parent survivor `N ≥ 6`. -/
theorem survivor_Nge7_open :
    multiplicityEvidence .properGammaNge7 = Evidence.openNode ∧
      multiplicityEvidence .properGammaNge6Parent = Evidence.openNode := ⟨rfl, rfl⟩

/-- **`numerical_closures_are_certificates`.**  `KERNEL-PROVED`.  The four numerical shell
closures are `CERTIFICATE_BACKED`, never `KERNEL_PROVED`. -/
theorem numerical_closures_are_certificates :
    multiplicityEvidence .properGammaQ200Closure = Evidence.certificateBacked ∧
      multiplicityEvidence .properGammaN1Closure = Evidence.certificateBacked ∧
      multiplicityEvidence .properGammaN2to5Closure = Evidence.certificateBacked ∧
      multiplicityEvidence .properGammaN6Closure = Evidence.certificateBacked ∧
      multiplicityEvidence .properGammaN6Closure ≠ Evidence.kernelProved :=
  ⟨rfl, rfl, rfl, rfl, by decide⟩

/-- **`exact_algebra_is_kernel_proved`.**  `KERNEL-PROVED`.  The exact algebra of this run is
kernel content. -/
theorem exact_algebra_is_kernel_proved :
    multiplicityEvidence .qFibreAlgebra = Evidence.kernelProved ∧
      multiplicityEvidence .laneRecombination = Evidence.kernelProved ∧
      multiplicityEvidence .multiplicityBandGeometry = Evidence.kernelProved ∧
      multiplicityEvidence .shellSixGeometry = Evidence.kernelProved ∧
      multiplicityEvidence .productChangeOfVariables = Evidence.kernelProved ∧
      multiplicityEvidence .lowerCutoffFirewall = Evidence.kernelProved ∧
      multiplicityEvidence .truncatedDivisorIdentity = Evidence.kernelProved ∧
      multiplicityEvidence .ownershipArithmetic = Evidence.kernelProved ∧
      multiplicityEvidence .parentChildNoDoubleCharge = Evidence.kernelProved :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`retired_nonclosing_methods`.**  `KERNEL-PROVED`.  The absolute Stieltjes-variation
extension into the complete many-multiple `t → 0` tail is recorded as a retired, nonclosing
method at the current wrapper scope — no lower bound for the physical signed source is
asserted anywhere.  The weighted `K_s` closing recurrence is open (only the exact count
identity is banked). -/
theorem retired_nonclosing_methods :
    multiplicityEvidence .absoluteVariationTail = Evidence.retiredNonclosingMethod ∧
      multiplicityEvidence .weightedKsRecurrence = Evidence.openNode := ⟨rfl, rfl⟩

/-- **`identity_factory_status`.**  `KERNEL-PROVED`.  The general identity landing is a legal
external input (conditional), while the closing prefix bound is open. -/
theorem identity_factory_status :
    multiplicityEvidence .identityFactoryLanding = Evidence.conditionalAnalytic ∧
      multiplicityEvidence .closingPrefixBound = Evidence.openNode := ⟨rfl, rfl⟩

/-- **`longFibre_preserved`.**  `KERNEL-PROVED`.  The long-fibre bank is preserved: its own
status ledger still records Erdős #287 as open, and its numerical ledger values are
unchanged. -/
theorem longFibre_preserved :
    longFibreStatus .erdos287 = LongFibreStatus.openNode ∧
      certifiedSubtotalV1000 = 5257263872 / 10 ^ 16 ∧
      remainingCapacityV1000 = 3603386128 / 10 ^ 16 := ⟨rfl, rfl, rfl⟩

/-! ## §41.3  Axiom audit for the proper-γ multiplicity additions -/

section AxiomAudit

-- §31 q-fibre reparametrisation
#print axioms qFibre_reparam
#print axioms qFibre_unique
#print axioms qFibre_proper
#print axioms beta_qFibre_mul
#print axioms beta_mul_not_general

-- §32 lane recombination
#print axioms lane_sign_transfer
#print axioms lane_recombination
#print axioms lane_recombination_z
#print axioms lane_signs_survive
#print axioms lane_range_restricted_no_cancellation

-- §33 multiplicity count and band geometry
#print axioms mem_multiplesIn
#print axioms multiplesIn_card
#print axioms NX_ge_iff_raw
#print axioms NX_ge_iff
#print axioms NX_eq_iff
#print axioms multAtLeast_iff
#print axioms bandsOf_one
#print axioms bandsOf_six
#print axioms bandsOf_seven
#print axioms shellOne_bands
#print axioms shellEq_disjoint
#print axioms shellCertificate_not_proved

-- §34 shell six
#print axioms shellSix_bands
#print axioms NX_eq_six_iff
#print axioms shellSix_disjoint_lower
#print axioms shellSix_certificate_not_proved

-- §35 the exact proper-γ source
#print axioms SGproper_eq
#print axioms SGproper_drop_qfilter
#print axioms SGproper_dead
#print axioms coprimality_marker_matters
#print axioms liveness_marker_matters

-- §36 the current survivor
#print axioms mem_omegaSevenPlus_iff
#print axioms NX_ge_seven_iff
#print axioms SGregion_split
#print axioms Rge7_split
#print axioms Rge7_not_bounded_here

-- §37 m = q n and the m > z firewall
#print axioms product_resummation
#print axioms lower_cutoff_matters
#print axioms bandIndex_ge_22
#print axioms bandIndex_exceptional
#print axioms bandIndex_chain
#print axioms geometry_not_arithmetic

-- §38 odd convolution and the factor-two error
#print axioms oddConvolution_identity
#print axioms abs_rhoOdd_le
#print axioms oddCount_exact
#print axioms oddError_bound
#print axioms factorTwo_Ez
#print axioms divisorMomentCertificate_not_proved

-- §39 the truncated divisor coefficient
#print axioms truncated_divisor_identity
#print axioms truncated_eq_complete_iff
#print axioms truncated_ne_complete

-- §40 the ownership ledger and the parent/child firewall
#print axioms allocatedTotal_eq
#print axioms childRemaining_eq
#print axioms parentAvailable_eq
#print axioms shell6_parent_recombine_legal
#print axioms parent_child_owner_disjoint
#print axioms shell6_double_charge_illegal
#print axioms global_ledger_unchanged

-- §41 status
#print axioms properGammaMultiplicity_open_frontier
#print axioms erdos287_open_multiplicity
#print axioms numerical_closures_are_certificates
#print axioms longFibre_preserved

end AxiomAudit

end Effectivity
end Erdos287
