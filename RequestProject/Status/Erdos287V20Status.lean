import Mathlib
import RequestProject.Erdos287.BalancedSevenV20Compiler
import RequestProject.Status.Erdos287V19Status

/-!
# Erdős #287 — V20 status: high-conductor character Gram / conductor router / HHH frontier

**ERDŐS #287 REMAINS OPEN.  BALANCED7 REMAINS OPEN.**  Nothing in V20 proves either, no
analytic or source interface is inhabited anywhere, and no `axiom` was added.

## 0. Regression guard

The pre-edit build was located and reused unchanged: the whole V16–V19 bank
(`FactorialEulerPolarization`, `FactorialEulerLocal`, `FactorialPolarizationLinearity`,
`PascadiParameterLedger`, `NormalForm3221`, `MovingPhaseProvider3221`,
`FactorialEndpoint3221Adapter`, `PrePoissonDensity3221`, `HighConductorVariance3221`,
`CharacterGram3221`, `BalancedSevenV19Compiler`, `Erdos287V18Status`,
`Erdos287V19Status`) is imported, not duplicated.  No existing declaration was restated,
renamed, weakened or deleted; V20 is append-only apart from import lines in
`RequestProject/Main.lean`.

In particular the V19 objects are *reused literally*: `CharGram3221.highSet`,
`CharGram3221.cHat`, `CharGram3221.cHigh`, `HighCond3221.InverseSampledHighCond3221Data`,
`HighCond3221.InverseSampledHighCondLogVar3221Input`,
`V19Compiler.CauchyPrefactor3221Certificate`, `V15Status.MuLogComparisonLowCondMatch`,
`V16Status.BalancedSevenPacketInput`.

## 1. Frontier reset

The V19 controlling node `3221-INVERSE-SAMPLED-HIGHCOND-LOGVAR45` is **not** deleted and
**not** declared false: it is now `REDUCED / CONDITIONAL COMPILER`, because V20 supplies an
exact four-channel reassembly (`V20HHH.logVar_of_four_channels`) whose only open analytic
antecedent is the surviving high-high-high shifted five-box character Gram.

The new first exact analytic residual is `3221-HIGHQUOTIENT-FIVEBOX-SHIFTED-GRAM45`.

The sixth-moment route `3221-HIGHCOND-RESIDUE-SIXTH-MOMENT45` is recorded as a *stronger
sufficient* open alternative and is deliberately **not** promoted to the controlling
frontier, notwithstanding its `1/105` conditional power margin.

## 2. What V20 adds (all sorry-free, kernel-checked)

* **Phase A** (`HighConductorCharacterGram3221.lean`): the literal high-conductor character
  set (`mem_highSet_iff_lt_conductor`, `sum_highSet_eq_sum_ite`); the inverse-sampled
  residue character algebra `affineSample`, `affineSample_mul_eq_one`,
  `affineSample_isUnit`, `affineSample_inv`, `affineSample_character_factor`,
  `inverseSample_character_identity`; and the expansion compiler
  `cHigh_inverseSampled_expansion` — all with the hypotheses `s² = 1`, `2m` invertible
  explicit.
* **Phase B** (`FiveBoxCharacterFactorization3221.lean`): `sum_mul_sum5`,
  `pairBlockSum_eq_mul`, `fiveBox_characterTransform_factor`,
  `fiveBox_characterTransform_eq_prod_five`.
* **Phase C**: `unitBox`, `shortMGram`, `highCoeff`, `autocorr`, `autocorr_reindex`,
  `charSrc_eq_cHigh_inverseSampled`, the abstract kernel `charSource_variance_eq_gram` and
  the central V20 theorem `inverseSampledVariance_eq_characterGram`.  Plus the
  same-primitive lift firewall `fixedModulus_samePrimitive_induced_unique`.
* **Phase D**: `characterGram_diag_split`, `autocorr_principal_eq_energy`,
  `autocorr_principal_highCoeff`; the external `PrimitiveConductorLargeSieve3221Input`
  (uninhabited) and the conditional `highCondDiagonal_of_largeSieve`; the exponent ledger
  `diagonal_fixed_power_room = 4/35`, `diagonal_power_room_rational`,
  `diagonal_power_room_rpow`.
* **Phase E**: `lowConductor_card_le` (proved finite conductor count), `lowQuotient_child_le`,
  `lowQuotient_child_of_diagonal_budget`.
* **Phase F**: `gram_parseval`, `autocorr_sup_le`, `autocorr_l2_sq_le`,
  `separateL2_compiler`, and the death certificate
  `separateGramL2_capacity_deficit` (`51/35 − 39/35 = 12/35 > 0`).
* **Phase G**: `PointwiseBurgess3221Input` (external, uninhabited, metadata only) and
  `pointwiseBurgess_capacity_deficit` (`879/560 − 624/560 = 51/112 > 0`).
* **Phase H**: `ConductorCell`, `RouterCondition`, `conductorCell_routed`, and the exact
  rational thresholds `router_case_A`, `router_case_B`, `router_case_C`,
  `router_threshold_identity`.
* **Phase I** (`HighQuotientShiftedGram3221.lean`): `SurvivingHHHConductorCell`,
  `HHHGramData`, `hhhGram`, the open socket
  `HighQuotientFiveBoxShiftedGram3221Input` with `hhhGram_input_not_automatic`, and the
  reassembly compiler `logVar_of_four_channels` together with the anti-circularity theorem
  `logVar_does_not_construct_hhh`.
* **Phase J** (`HighConductorSixthMoment3221.lean`): `sixthMoment`, `injOn_affineSample`,
  `sampled_sixth_le`, `sixthMoment_holder_at`, `sixthMoment_holder_over_q`,
  `HighCondResidueSixthMoment3221Input` (uninhabited), `sixthMoment_variance_exponent`,
  `sixthMoment_power_margin` (`117/105 − 116/105 = 1/105 > 0`).
* **Phases K/L/Q** (`BalancedSevenV20Compiler.lean`): `highConductorCutoff`,
  `MuLogComparisonAtCutoff`, `comparison_cutoff_must_match`,
  `balancedSeven_of_v20_package`, `v20_package_cutoff_consistent`, and the non-vacuity
  bank.

## 3. Final V20 ledger

```
FACTORIAL EULER                      : LEAN_PROVED               (V16, unchanged)
FIVE-BOX FACTORISATION               : LEAN_PROVED_FINITE
HIGHCOND CHARACTER EXPANSION         : LEAN_PROVED_FINITE
m-SAMPLED CHARACTER GRAM             : LEAN_PROVED_FINITE
HIGHCOND DIAGONAL                    : EXTERNAL ANALYTIC / CONDITIONAL COMPILER
LOW-QUOTIENT COLLAPSE                : EXTERNAL ANALYTIC / CONDITIONAL COMPILER
SEPARATE-GRAM L2                     : CAPACITY NONCLOSING BY 12/35
POINTWISE BURGESS                    : EXTERNAL CAPACITY NONCLOSING GLOBALLY
BURGESS CONDUCTOR-PAIR ROUTER        : CONDITIONAL EXTERNAL PASS
MODERATE CONDUCTOR CELLS             : ROUTED CONDITIONALLY ON EXTERNAL INPUTS
HIGHQUOTIENT-FIVEBOX-SHIFTED-GRAM45  : OPEN_ANALYTIC / FIRST EXACT RESIDUAL
HIGHCOND RESIDUE SIXTH MOMENT        : STRONGER SUFFICIENT / OPEN
INVERSE-SAMPLED HIGHCOND LOGVAR      : REDUCED / CONDITIONAL COMPILER
COMPARISON                           : SOURCE_OPEN
BALANCED7                            : OPEN
FCL                                  : OPEN
GATE2                                : OPEN
WINDOWPAIRSUPPLY                     : OPEN
ERDOS287                             : OPEN
```
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V20Status

/-! ## The machine-readable V20 ledger

This is **metadata**: a function on a finite index type.  No theorem in this repository
converts a ledger value into a mathematical claim, and in particular no external analytic
theorem is promoted to a Lean-proved statement by any label below. -/

/-- The V20 status nodes. -/
inductive Node
  | factorialEuler
  | fiveBoxFactorisation
  | highCondCharacterExpansion
  | mSampledCharacterGram
  | highCondDiagonal
  | lowQuotientCollapse
  | separateGramL2
  | pointwiseBurgess
  | burgessConductorPairRouter
  | moderateConductorCells
  | highQuotientFiveBoxShiftedGram
  | highCondResidueSixthMoment
  | inverseSampledHighCondLogVar
  | comparison
  | balancedSeven
  | fcl
  | gate2
  | windowPairSupply
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- The V20 status labels. -/
inductive Label
  | leanProved
  | leanProvedFinite
  | externalAnalyticConditionalCompiler
  | capacityNonclosing12over35
  | externalCapacityNonclosingGlobally
  | conditionalExternalPass
  | routedConditionalOnExternalInputs
  | openAnalyticFirstResidual
  | strongerSufficientOpen
  | reducedConditionalCompiler
  | sourceOpen
  | openNode
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The V20 ledger. -/
def ledger : Node → Label
  | factorialEuler => leanProved
  | fiveBoxFactorisation => leanProvedFinite
  | highCondCharacterExpansion => leanProvedFinite
  | mSampledCharacterGram => leanProvedFinite
  | highCondDiagonal => externalAnalyticConditionalCompiler
  | lowQuotientCollapse => externalAnalyticConditionalCompiler
  | separateGramL2 => capacityNonclosing12over35
  | pointwiseBurgess => externalCapacityNonclosingGlobally
  | burgessConductorPairRouter => conditionalExternalPass
  | moderateConductorCells => routedConditionalOnExternalInputs
  | highQuotientFiveBoxShiftedGram => openAnalyticFirstResidual
  | highCondResidueSixthMoment => strongerSufficientOpen
  | inverseSampledHighCondLogVar => reducedConditionalCompiler
  | comparison => sourceOpen
  | balancedSeven => openNode
  | fcl => openNode
  | gate2 => openNode
  | windowPairSupply => openNode
  | erdos287 => openNode

/-- **The first exact analytic residual is unique.**  `3221-HIGHQUOTIENT-FIVEBOX-SHIFTED-
GRAM45` is the *only* node carrying `OPEN_ANALYTIC / FIRST EXACT RESIDUAL`. -/
theorem controlling_analytic_residual_unique (n : Node) :
    ledger n = openAnalyticFirstResidual ↔ n = highQuotientFiveBoxShiftedGram := by
  revert n
  decide +kernel

/-- The sixth-moment route is recorded as a *stronger sufficient* open alternative and is
**not** the controlling frontier. -/
theorem sixthMoment_not_controlling :
    ledger highCondResidueSixthMoment = strongerSufficientOpen ∧
      strongerSufficientOpen ≠ openAnalyticFirstResidual ∧
      strongerSufficientOpen ≠ leanProved ∧ strongerSufficientOpen ≠ leanProvedFinite := by
  decide +kernel

/-- The V19 log-variance node is `REDUCED / CONDITIONAL COMPILER`: neither proved nor
refuted, and distinct from every "proved" label. -/
theorem logVar_reduced_not_proved :
    ledger inverseSampledHighCondLogVar = reducedConditionalCompiler ∧
      reducedConditionalCompiler ≠ leanProved ∧
      reducedConditionalCompiler ≠ leanProvedFinite ∧
      reducedConditionalCompiler ≠ openAnalyticFirstResidual := by
  decide +kernel

/-- The two capacity firewalls carry labels distinct from every "proved" label: they are
audits of exponent arithmetic, not theorems about external results. -/
theorem capacity_firewalls_are_not_proofs :
    ledger separateGramL2 = capacityNonclosing12over35 ∧
      ledger pointwiseBurgess = externalCapacityNonclosingGlobally ∧
      capacityNonclosing12over35 ≠ leanProved ∧
      externalCapacityNonclosingGlobally ≠ leanProved := by
  decide +kernel

/-- The diagonal and low-quotient children are conditional on **external** analytic inputs
and are never relabelled `LEAN_PROVED`. -/
theorem children_are_conditional :
    ledger highCondDiagonal = externalAnalyticConditionalCompiler ∧
      ledger lowQuotientCollapse = externalAnalyticConditionalCompiler ∧
      ledger moderateConductorCells = routedConditionalOnExternalInputs ∧
      externalAnalyticConditionalCompiler ≠ leanProved ∧
      routedConditionalOnExternalInputs ≠ leanProved := by
  decide +kernel

/-- The comparison node stays `SOURCE_OPEN`. -/
theorem comparison_source_open :
    ledger comparison = sourceOpen ∧ sourceOpen ≠ leanProved := by
  decide +kernel

/-- The five terminal nodes stay open. -/
theorem terminal_nodes_open :
    ledger balancedSeven = openNode ∧ ledger fcl = openNode ∧ ledger gate2 = openNode ∧
      ledger windowPairSupply = openNode ∧ ledger erdos287 = openNode := by
  decide +kernel

end V20Status
end Erdos287
