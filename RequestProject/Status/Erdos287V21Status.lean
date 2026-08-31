import Mathlib
import RequestProject.Erdos287.BalancedSevenV21Compiler
import RequestProject.Status.Erdos287V20Status

/-!
# Erdős #287 — V21 status: the two-high-projector / five-box sieve safe repair bank

**ERDŐS #287 REMAINS OPEN.  BALANCED7 REMAINS OPEN.**  No V21 statement proves either, no
source or external analytic interface is inhabited, and no `axiom` was added.

## 0. Relation to V20

V20 is preserved verbatim.  In particular `shortMGram`, `autocorr`,
`inverseSampledVariance_eq_characterGram`, the conductor router, the separate-`L²` death
certificate, the Burgess capacity firewall, `HighQuotientFiveBoxShiftedGram3221Input`, the
sixth-moment bridge and the same-`B0` comparison firewall are all imported and reused.  The
V20 HHH representation is **valid and historical**; it is *not* deleted and *not* declared
false.  What is retracted is the **old HHH inclusion–exclusion argument as a closure
proof**: the conductor-cell inclusion–exclusion over quotient conductors does not, by
itself, produce a complete four-cell reassembly, so it is superseded as the controlling
route by the exact two-projector identity

```
HIGH-HIGH = AA − BA − AB + BB,
```

which needs no quotient conductor and no Burgess conductor-cell inclusion–exclusion.

## 1. What V21 adds (all sorry-free, kernel-checked)

* `TwoHighProjector3221.lean` — `highIndicator_eq_one_sub_badIndicator`,
  `twoHighProjector_pointwise`, `highHighSum_eq_AA_sub_BA_sub_AB_add_BB`,
  `twoProjector_no_double_counting`, the ambient firewall
  `TwoProjectorAmbientCompat3221`, the reconstructed pre-projector variance
  (`preProjectorVariance`, `preProjectorVariance_eq_AA`, and the *proved* equivalence with
  the V20 `ξ`-representation `preProjectorVariance_eq_xiForm`), the literal high-conductor
  support lemma `preProjectorVariance_highSet_support`, and the four `q`-summed channels
  with `VhiHigh_eq_channels`.
* `DoubleOrthogonalityFiveBox3221.lean` — `fullFull_orthogonality_left/right`,
  `affine_congruence_iff_dvd` (both sign branches), `doubleOrthogonality_congruence`,
  `doubleOrthogonality_shift_exists`, `doubleOrthogonality_affineDivisor`,
  `doubleOrthogonality_coprime`, `fiveProduct`, `char_fiveProduct`, `fiveBox_shift_exists`.
* `BadCharacterCount3221.lean` — the **repair**: `badCharacter_card_le_sum_totient`,
  `badCharacter_card_le_triangular`, `badCharacter_card_le_sq`, `dirichletBad_card_le_sq`,
  and `highSetOf_badSet_eq_highSet`.  The unsafe `D·τ(q)` heuristic is not banked.
* `PrimeBoxNormalization3221.lean` — the source audit (no physical `ω_i` in the
  repository), the uninhabited `BalancedSevenPrimeBoxNormalization3221`, the conditional
  `primeBoxL1_of_pointwise_and_count`, and the abstract phase lemmas
  `phaseUniformBound_implies_sum_abs_omega_le_seven` /
  `phaseUniformBound_implies_each_abs_omega_le_seven`.
* `ShortShiftSieve3221.lean` — the Lean-proved geometry
  `shortShiftGeometry_of_doubleOrthogonality` and the uninhabited external interface
  `ShortShiftRoughSieve3221Input` with its parameter metadata (`z = T^{1/20}`, dimension 1,
  negligible `z²` remainder).
* `ShiuDivisorAverage3221.lean` — `totient_two_mul_of_odd`, `shiuLocalFactor_eq`, and the
  uninhabited `ShiuLinearDivisorAverage3221Input`.
* `HighProjectorCutoff3221.lean` — the shared cutoff `sharedCutoff`,
  `HighProjectorCutoffCompat3221`, `cutoffCompat_cutoffs_match`,
  `cutoffCompat_matches_v20_comparison`, `cutoffCompat_does_not_fix_B0`.
* `PhysicalLogBudget3221.lean` — the exponent ledger (`twoProjector_naturalExponent`,
  `outerCauchy_exponent`, `physicalSquareRoot_exponent`), the symbolic log budget
  (`projectorLogExponent`, `highVarianceLogCompiler`, `outerCauchyLogCompiler`) and the
  uninhabited `PhysicalLogPrefactor3221` with `prefactor_enters_log_ledger`.
* `OuterTwoPrimeBlock3221.lean` — `outerInnerBox_disjoint`, `outerInnerBox_cover`,
  `sevenBox_partition_cardinality`, `primeDensity_no_double_spending`, `alphaOuter`,
  `alphaOuter_l1_le`, `outerL2_of_sup_and_l1`, and the uninhabited
  `OuterTwoPrimeL2Normalization3221Input`.
* `BalancedSevenV21Compiler.lean` — the four separate channel bounds, the budget layer
  `TwoHighProjector3221ClosureInputs`, `twoHighProjector3221_closes_logVar`, the package
  `TwoHighProjector3221SourcePackage`, `logVar_of_twoHighProjectorPackage`,
  `balancedSeven_of_v21_package`, `sixthMoment_not_needed_if_twoProjectorClosed`, and the
  non-vacuity bank.

## 2. Residual order

```
1. BALANCED7-PRIMEBOX-L1-NORMALIZATION45   SOURCE_OPEN   (first exact residual)
2. 3221-HIGHPROJECTOR-CUTOFF-COMPAT45      SOURCE_OPEN
3. 3221-PHYSICAL-LOG-PREFAC45              SOURCE_OPEN
4. BA/AB/BB analytic bounds under the repaired safe bad-character count
5. COMPARISON                              SOURCE_OPEN (not yet the frontier)
```
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace V21Status

/-! ## The machine-readable V21 ledger

This is **metadata**: functions on a finite index type.  No theorem converts a ledger value
into a mathematical claim. -/

/-- The V21 status nodes. -/
inductive Node
  | v20CharacterGram
  | v20HHHRoute
  | oldHHHInclusionExclusionClosureProof
  | twoHighProjectorReassembly
  | doubleOrthogonality
  | safeBadCharacterCount
  | shiuInterface
  | shortShiftSieveInterface
  | primeBoxNormalization
  | cutoffCompatibility
  | physicalLogPrefactor
  | twoProjectorClosure
  | inverseSampledHighCondLogVar
  | sixthMoment
  | comparison
  | balancedSeven
  | fcl
  | gate2
  | windowPairSupply
  | erdos287
  deriving DecidableEq, Fintype, Repr

/-- The V21 status labels. -/
inductive Label
  | banked
  | validHistoricalNotControlling
  | retracted
  | algebraicPass
  | exactPass
  | finitePass
  | externalAnalyticUninhabited
  | sourceOpen
  | conditional
  | openConditional
  | openStrongerSufficientFallback
  | conditionalNotActivated
  | openNode
  deriving DecidableEq, Fintype, Repr

open Node Label

/-- The V21 ledger. -/
def ledger : Node → Label
  | v20CharacterGram => banked
  | v20HHHRoute => validHistoricalNotControlling
  | oldHHHInclusionExclusionClosureProof => retracted
  | twoHighProjectorReassembly => algebraicPass
  | doubleOrthogonality => exactPass
  | safeBadCharacterCount => finitePass
  | shiuInterface => externalAnalyticUninhabited
  | shortShiftSieveInterface => externalAnalyticUninhabited
  | primeBoxNormalization => sourceOpen
  | cutoffCompatibility => sourceOpen
  | physicalLogPrefactor => sourceOpen
  | twoProjectorClosure => conditional
  | inverseSampledHighCondLogVar => openConditional
  | sixthMoment => openStrongerSufficientFallback
  | comparison => sourceOpen
  | balancedSeven => openNode
  | fcl => openNode
  | gate2 => conditionalNotActivated
  | windowPairSupply => openNode
  | erdos287 => openNode

/-- The residual order: `1` is the current first exact residual, `0` means "not on the
residual list". -/
def residualRank : Node → ℕ
  | primeBoxNormalization => 1
  | cutoffCompatibility => 2
  | physicalLogPrefactor => 3
  | comparison => 4
  | _ => 0

/-- **The V20 HHH route is valid and historical, but not controlling in V21.** -/
theorem v20_hhh_route_not_controlling_v21 :
    ledger v20HHHRoute = validHistoricalNotControlling ∧
      validHistoricalNotControlling ≠ retracted ∧
      validHistoricalNotControlling ≠ conditional ∧
      ledger v20CharacterGram = banked := by
  decide +kernel

/-- **The old HHH inclusion–exclusion *closure proof* is retracted** — as a closure proof
only; the HHH Gram object and its socket are untouched. -/
theorem oldHHH_closure_proof_retracted :
    ledger oldHHHInclusionExclusionClosureProof = retracted ∧
      retracted ≠ validHistoricalNotControlling ∧ retracted ≠ banked := by
  decide +kernel

/-- **The V21 two-projector route is the current controlling conditional route.** -/
theorem v21_twoProjector_route_controlling :
    ledger twoHighProjectorReassembly = algebraicPass ∧
      ledger doubleOrthogonality = exactPass ∧
      ledger safeBadCharacterCount = finitePass ∧
      ledger twoProjectorClosure = conditional ∧
      conditional ≠ banked := by
  decide +kernel

/-- **The current first exact residual is the prime-box `L¹` normalisation.** -/
theorem first_exact_residual_is_primeBoxNormalization :
    ledger primeBoxNormalization = sourceOpen ∧ residualRank primeBoxNormalization = 1 ∧
      ∀ n : Node, residualRank n = 1 → n = primeBoxNormalization := by
  decide +kernel

/-- **Comparison is not the current frontier**: it is `SOURCE_OPEN` but strictly later in
the residual order than the three two-projector source pins. -/
theorem comparison_not_first_residual :
    ledger comparison = sourceOpen ∧
      residualRank primeBoxNormalization < residualRank comparison ∧
      residualRank cutoffCompatibility < residualRank comparison ∧
      residualRank physicalLogPrefactor < residualRank comparison := by
  decide +kernel

/-- The two external analytic interfaces stay uninhabited external candidates. -/
theorem external_interfaces_uninhabited :
    ledger shiuInterface = externalAnalyticUninhabited ∧
      ledger shortShiftSieveInterface = externalAnalyticUninhabited ∧
      externalAnalyticUninhabited ≠ banked ∧
      externalAnalyticUninhabited ≠ finitePass := by
  decide +kernel

/-- The log-variance node is conditional and **not** closed. -/
theorem logVar_open_conditional :
    ledger inverseSampledHighCondLogVar = openConditional ∧
      openConditional ≠ banked ∧ openConditional ≠ finitePass ∧
      openConditional ≠ algebraicPass := by
  decide +kernel

/-- The sixth moment stays an open stronger sufficient fallback; it is not marked false and
not retired. -/
theorem sixthMoment_open_stronger_fallback :
    ledger sixthMoment = openStrongerSufficientFallback ∧
      openStrongerSufficientFallback ≠ retracted ∧
      openStrongerSufficientFallback ≠ banked := by
  decide +kernel

/-- The terminal nodes stay open. -/
theorem terminal_nodes_open_v21 :
    ledger balancedSeven = openNode ∧ ledger fcl = openNode ∧
      ledger gate2 = conditionalNotActivated ∧ ledger windowPairSupply = openNode ∧
      ledger erdos287 = openNode := by
  decide +kernel

end V21Status
end Erdos287
