import Mathlib
import RequestProject.Erdos287.CurrentStatusEffectivityMultiplicity
import RequestProject.Erdos287.ProperGammaAdmission
import RequestProject.Erdos287.Early4490FiniteACompiler
import RequestProject.Erdos287.Early4490BernoulliJet
import RequestProject.Erdos287.Early4490RationalJetSource
import RequestProject.Erdos287.Early4490FiniteDFT
import RequestProject.Erdos287.Early4490NearResonance
import RequestProject.Erdos287.Early4490RationalJetLedger

/-!
# Erdős #287 effectivity — status after the EARLY_4490 rational-jet run (§49)

This file **extends** `CurrentStatusEffectivity`, `CurrentStatusEffectivityLongFibre` and
`CurrentStatusEffectivityMultiplicity`.  Nothing earlier is rewritten: the long-fibre bank and
the proper-γ multiplicity bank remain trusted at their declared scope, and their theorem
statements are untouched.

```
LONG-FIBRE:                        BANKED / HISTORICAL
PROPER-GAMMA MULTIPLICITY LAYER:   BANKED
q ≤ 200:                           CERTIFICATE-BACKED CLOSED
N = 1:                             CERTIFICATE-BACKED CLOSED
N = 2..5:                          CERTIFICATE-BACKED CLOSED
shell N = 6:                       CERTIFICATE-BACKED in CHILD chart
recombined N ≥ 6:                  ACTIVE PARENT chart
late subslab:                      CLOSED AT DECLARED CERTIFICATE SCOPE
EARLY_4490:                        STRICTLY REDUCED / OPEN
reciprocal integral:               REMOVED AT DECLARED DIRECTED COST
J3:                                OPEN
Jψ:                                OPEN ALTERNATIVE
signed near-resonant aggregate:    OPEN
selected Perron:                   OPEN
proper gamma (full slab):          OPEN
S_live:                            OPEN
R_012:                             OPEN
signed floor:                      OPEN
Maynard:                           NOT ENTERED
final splice:                      OPEN
ERDŐS #287:                        OPEN
```

The live frontier coordinate is `EARLY_4490_RATIONAL_JET`.
`early4490RationalJet_open_frontier` proves that no open node of that frontier is tagged
closed, and no open proposition anywhere in this layer is inhabited.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Effectivity

/-! ## §49.1  Retired-method statuses -/

/-- Statuses for methods that are no longer part of the live chart. -/
inductive MethodStatus
  | superseded
  | rejectedFalse
  | renamedWall
  | methodNonclosing
  | stillOpen
  deriving DecidableEq, Repr

/-- The retired / renamed methods of the current run. -/
inductive RetiredMethod
  | reciprocalIntegralControl
  | pointwiseSmallFourierRemainder
  | coefficientOnlyR1C2Merge
  | positiveWholeEarlySlabWrapper
  | signedNearResonantAggregate
  | selectedPerron
  deriving DecidableEq, Repr

/-- The recorded status of each retired / renamed method. -/
def retiredStatus : RetiredMethod → MethodStatus
  | .reciprocalIntegralControl => .superseded
  | .pointwiseSmallFourierRemainder => .rejectedFalse
  | .coefficientOnlyR1C2Merge => .renamedWall
  | .positiveWholeEarlySlabWrapper => .methodNonclosing
  | .signedNearResonantAggregate => .stillOpen
  | .selectedPerron => .stillOpen

/-- **`retired_method_firewalls`.**  `KERNEL-PROVED`.  The recorded statuses.  No universal
impossibility theorem is encoded: these are bookkeeping tags for the current chart only. -/
theorem retired_method_firewalls :
    retiredStatus .reciprocalIntegralControl = MethodStatus.superseded ∧
      retiredStatus .pointwiseSmallFourierRemainder = MethodStatus.rejectedFalse ∧
      retiredStatus .coefficientOnlyR1C2Merge = MethodStatus.renamedWall ∧
      retiredStatus .positiveWholeEarlySlabWrapper = MethodStatus.methodNonclosing ∧
      retiredStatus .signedNearResonantAggregate = MethodStatus.stillOpen ∧
      retiredStatus .selectedPerron = MethodStatus.stillOpen :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §49.2  The tracked nodes of the EARLY_4490 frontier -/

/-- The nodes tracked after the EARLY_4490 rational-jet run. -/
inductive Early4490Node
  | longFibreBankHistorical
  | properGammaMultiplicityBank
  | q200Closure
  | n1Closure
  | n2to5Closure
  | shellSixChildClosure
  | recombinedParentChart
  | gammaParameterAlgebra
  | highPrimeCountBound
  | admissionInclusionExclusion
  | c3SourceTyping
  | c3RemainderCertificate
  | ownershipArithmetic
  | slabPartition
  | lateSubslabClosure
  | rangeDataCertificates
  | finiteACompiler
  | finiteAPartialSummation
  | bernoulliJetAlgebra
  | threeTermJetDefinition
  | eulerBernoulliIdentity
  | jetSourceDefinitions
  | replacementCertificates
  | budgetArithmetic
  | alternativeChartFirewall
  | finiteQDFT
  | zeroModes
  | nearResonantIdentity
  | early4490Reduction
  | j3AnalyticBound
  | jpsiAnalyticBound
  | signedNearResonantAggregateNode
  | selectedPerronNode
  | properGammaFullSlab
  | sLive
  | r012
  | signedFloor
  | maynard
  | finalSplice
  | erdos287
  deriving DecidableEq, Repr

/-- The evidence class of each tracked node (reusing the §41 taxonomy). -/
def early4490Evidence : Early4490Node → Evidence
  | .longFibreBankHistorical => .certificateBacked
  | .properGammaMultiplicityBank => .certificateBacked
  | .q200Closure => .certificateBacked
  | .n1Closure => .certificateBacked
  | .n2to5Closure => .certificateBacked
  | .shellSixChildClosure => .certificateBacked
  | .recombinedParentChart => .kernelProved
  | .gammaParameterAlgebra => .kernelProved
  | .highPrimeCountBound => .kernelProved
  | .admissionInclusionExclusion => .kernelProved
  | .c3SourceTyping => .kernelProved
  | .c3RemainderCertificate => .certificateBacked
  | .ownershipArithmetic => .kernelProved
  | .slabPartition => .kernelProved
  | .lateSubslabClosure => .certificateBacked
  | .rangeDataCertificates => .certificateBacked
  | .finiteACompiler => .kernelProved
  | .finiteAPartialSummation => .kernelProved
  | .bernoulliJetAlgebra => .kernelProved
  | .threeTermJetDefinition => .kernelProved
  | .eulerBernoulliIdentity => .conditionalAnalytic
  | .jetSourceDefinitions => .kernelProved
  | .replacementCertificates => .certificateBacked
  | .budgetArithmetic => .kernelProved
  | .alternativeChartFirewall => .kernelProved
  | .finiteQDFT => .kernelProved
  | .zeroModes => .kernelProved
  | .nearResonantIdentity => .kernelProved
  | .early4490Reduction => .openNode
  | .j3AnalyticBound => .openNode
  | .jpsiAnalyticBound => .openNode
  | .signedNearResonantAggregateNode => .openNode
  | .selectedPerronNode => .openNode
  | .properGammaFullSlab => .openNode
  | .sLive => .openNode
  | .r012 => .openNode
  | .signedFloor => .openNode
  | .maynard => .notEntered
  | .finalSplice => .openNode
  | .erdos287 => .openNode

/-- The nodes that must remain unclosed after this run. -/
def early4490OpenNodes : List Early4490Node :=
  [.early4490Reduction, .j3AnalyticBound, .jpsiAnalyticBound, .signedNearResonantAggregateNode,
   .selectedPerronNode, .properGammaFullSlab, .sLive, .r012, .signedFloor, .maynard,
   .finalSplice, .erdos287, .eulerBernoulliIdentity]

/-- **`early4490RationalJet_open_frontier`.**  `KERNEL-PROVED`.  No node of the EARLY_4490 open
frontier is tagged `kernelProved` or `certificateBacked`; in particular none is closed.  Erdős
#287 is recorded `OPEN` and Maynard `NOT ENTERED`. -/
theorem early4490RationalJet_open_frontier :
    (∀ n ∈ early4490OpenNodes,
        early4490Evidence n ≠ Evidence.kernelProved ∧
          early4490Evidence n ≠ Evidence.certificateBacked ∧
          (early4490Evidence n).isClosed = false) ∧
      early4490Evidence .erdos287 = Evidence.openNode ∧
      early4490Evidence .maynard = Evidence.notEntered := by
  refine ⟨by decide, rfl, rfl⟩

/-- **`early4490_kernel_layer`.**  `KERNEL-PROVED`.  The exact algebra delivered by this run is
kernel content, and the analytic replacement/late-subslab inputs are certificates. -/
theorem early4490_kernel_layer :
    early4490Evidence .highPrimeCountBound = Evidence.kernelProved ∧
      early4490Evidence .admissionInclusionExclusion = Evidence.kernelProved ∧
      early4490Evidence .finiteACompiler = Evidence.kernelProved ∧
      early4490Evidence .finiteAPartialSummation = Evidence.kernelProved ∧
      early4490Evidence .finiteQDFT = Evidence.kernelProved ∧
      early4490Evidence .zeroModes = Evidence.kernelProved ∧
      early4490Evidence .nearResonantIdentity = Evidence.kernelProved ∧
      early4490Evidence .budgetArithmetic = Evidence.kernelProved ∧
      early4490Evidence .alternativeChartFirewall = Evidence.kernelProved ∧
      early4490Evidence .replacementCertificates = Evidence.certificateBacked ∧
      early4490Evidence .lateSubslabClosure = Evidence.certificateBacked ∧
      early4490Evidence .eulerBernoulliIdentity = Evidence.conditionalAnalytic :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`banked_layers_preserved`.**  `KERNEL-PROVED`.  The long-fibre and proper-γ multiplicity
banks are preserved: their status ledgers still record Erdős #287 as open and their numerical
values are unchanged. -/
theorem banked_layers_preserved :
    multiplicityEvidence .erdos287 = Evidence.openNode ∧
      longFibreStatus .erdos287 = LongFibreStatus.openNode ∧
      certifiedSubtotalV1000 = 5257263872 / 10 ^ 16 ∧
      remainingCapacityV1000 = 3603386128 / 10 ^ 16 ∧
      properGammaTarget = 7204976032 / 10 ^ 17 ∧
      parentAvailable = 814976032 / 10 ^ 17 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §49.3  Axiom audit for the EARLY_4490 additions -/

section AxiomAudit

-- §42 γ parameters, high-prime admission, inclusion–exclusion
#print axioms gammaPar_eq_a0_add_half_nu
#print axioms four_nuPar_gt_gammaPar
#print axioms admission_threshold_pow
#print axioms highPrimeCount_le_three
#print axioms highPrime_four_impossible
#print axioms gammaAdmission_inclusion_exclusion
#print axioms admissionE_exceptional_case
#print axioms admissionE_coeff_two_forced
#print axioms admission_no_four_case
#print axioms admC3_endpoint_firewall
#print axioms c3_source_typing
#print axioms c3Certificate_not_proved

-- §43 the finite-a compiler
#print axioms wCoef_eq_mu_B_div_B1
#print axioms MtruncN_dvd
#print axioms largePrime_mask_irrelevant
#print axioms Pcompiler_eq_zero_of_gt
#print axioms finiteA_compiler_untruncated
#print axioms finiteA_compiler
#print axioms abel_summation_general
#print axioms Fcompiler_succ_sub
#print axioms finiteA_partial_summation
#print axioms compiler_not_fibre_annihilation

-- §44 Bernoulli algebra and the three-term jet
#print axioms psiSaw_endpoint
#print axioms bern2_values
#print axioms bern3_values
#print axioms bern2_reflect
#print axioms bern3_reflect
#print axioms psiSaw_reflect
#print axioms bernoulli_derivative_ladder
#print axioms Phi3_eq
#print axioms Phi3_sub_PhiPsi
#print axioms Phi3_additive_in_jet
#print axioms bernoulliJet_downstream_algebra
#print axioms bernoulliJetIdentity_not_proved

-- §45 the early joint source and the rational-jet charts
#print axioms omegaEarly_eq
#print axioms Jjoint_linear_decomposition
#print axioms joint_split_charging_firewall
#print axioms J3src_eq
#print axioms Jpsisrc_eq
#print axioms rationalJet_charts_are_alternatives
#print axioms J3src_eq_Jpsisrc_of_flat_jet
#print axioms earlyJoint_target_open

-- §46 finite q-DFT and the zero modes
#print axioms dftCoef_eq
#print axioms finite_dft_inversion
#print axioms dftCoef_zero_eq_zeroMode
#print axioms sum_range_bern2
#print axioms coprime_sum_mobius
#print axioms mobius_id_divisors_squarefree
#print axioms f1_zero_mode
#print axioms f2_zero_mode
#print axioms f3_zero_mode
#print axioms f1_zeroMode_needs_q_gt_one
#print axioms maskedCorrection_zero_mean
#print axioms f2_zeroMode_mask_firewall

-- §47 the near-resonant odd identity
#print axioms rhoOdd_near_odd
#print axioms sum_divisors_hz_odd
#print axioms nearResonance_identity
#print axioms nearResonance_no_smallness

-- §48 the rational-jet ledger
#print axioms c3_ownership_arithmetic
#print axioms slab_partition
#print axioms slab_endpoints_exact
#print axioms lateSubslab_certificate_not_proved
#print axioms early4490_range_arithmetic
#print axioms range_integer_consequence
#print axioms target3_budget_arithmetic
#print axioms targetPsi_budget_arithmetic
#print axioms replacement_certificates_not_proved
#print axioms chart_budget_closes
#print axioms rationalJet_alternative_chart_no_double_charge
#print axioms numerical_certificates_not_theorems

-- §49 status
#print axioms retired_method_firewalls
#print axioms early4490RationalJet_open_frontier
#print axioms early4490_kernel_layer
#print axioms banked_layers_preserved

end AxiomAudit

end Effectivity
end Erdos287
