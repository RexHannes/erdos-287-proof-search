import Mathlib
import RequestProject.Status.CurrentStatusErdos287TransverseBezoutSingleCarrier
import RequestProject.CurrentProgramme.Erdos287TransverseAffineProductEnergyInterface
import RequestProject.CurrentProgramme.Erdos287ReciprocalDensityDuality

/-!
# Append-only status layer — Erdős #287, dual-level / simultaneous-critical frontier

This module is **append-only**.  The earlier ledgers (C0 unitary Fourier, transverse carrier,
one-conductor / Bézout single carrier) are re-checked, never edited; the preservation theorems of
§7 record that their rows are unchanged.

```
C0:                          conditionalSourcePin  (analytically closed *conditional* on the
                                                    formal source normalisation).
EXACT PRODUCT COLLISION:     analyticBanked.
DOUBLE TYPE II (287-local):  analyticBanked.

TRANSVERSE ONE-CONDUCTOR RECIPROCITY45 : analyticBanked.
qC UNITARYFOURIER45                    : analyticBanked.
BEZOUT THREE-AXIS45                    : analyticBanked (finite theorems kernelProved).
DUAL-LEVEL RECIPROCITY45               : analyticBanked (finite theorems kernelProved).
DUAL PAIRWISE FOURIER45                : analyticBanked (finite theorems kernelProved).
RECIPROCAL-DENSITY DUALITY45           : analyticBanked (identities kernelProved).
AFFINE-PRODUCT ENERGY45                : conditionalSourcePin (weighted Ω norm).

OLD SATURATION FACE:                     superseded (not false).
SINGLE-CARRIER45:                        superseded as first frontier (not false).
ULTRANEAR-CRITICALDENSITY-MOBIUSLEVEL45: superseded / strictly reduced (not false).

CURRENT FIRST ANALYTIC RESIDUAL:
    THREEFACTOR-TRANSVERSE-BRANCHI-SIMULTANEOUSCRITICAL-DUALLEVEL-AFFINEPRODUCT-MOBIUS45 : open.

FULL TRANSVERSE:  strictReduction / open.
b-DIAGONAL:       open / untouched.
ERDOS287:         open.
```

`ResearchStatus` is metadata: **no value of it carries any implication of mathematical truth**.
The `kernelProved` rows of this delta are exactly the finite arithmetic / finite Fourier rows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace SimultaneousCriticalStatus

open Erdos287.C0UnitaryFourierStatus
open ResearchStatus

/-! ## §1  Nodes of the dual-level ledger -/

/-- Nodes of the dual-level / simultaneous-critical ledger. -/
inductive DualLevelNode
  /-- Bézout-row affine CRT algebra (`γ_g` mod `m`, mod `r₀`, affine injectivity). -/
  | bezoutRowAffineAlgebra
  /-- Bézout three-axis frequency fibre theorem. -/
  | bezoutThreeAxisFibre
  /-- Bézout three-axis finite Fourier inequality. -/
  | bezoutThreeAxisFourier
  /-- Large-`g` router: the elementary residue-class core only. -/
  | largeGResidueCore
  /-- Large-`g` router: the weighted harmonic tail. -/
  | largeGWeightedRouter
  /-- All-`q` atomic grouped compiler (conditional on grouped product energy). -/
  | allQAtomicGroupedCompiler
  /-- Dual CRT split of the reciprocal phase. -/
  | dualCRTSplit
  /-- Additive reciprocity for the `r₀`-component. -/
  | additiveReciprocity
  /-- Dual `Ξ` normal form (`C_{mqg}`, affine slope). -/
  | dualXiNormalForm
  /-- Constant `Ξ`-gcd and reduced modulus. -/
  | constantXiGcd
  /-- Variable `Ξ`-gcd, reduced coprimality. -/
  | variableXiGcd
  /-- Large-`Ξ`-gcd weighted router (interface only). -/
  | largeXiGcdRouter
  /-- Dual frequency fibre bounds. -/
  | dualFrequencyFibres
  /-- Dual pairwise finite Fourier inequalities. -/
  | dualPairwiseFourier
  /-- Packetwise minimum (no-double-spending) firewall. -/
  | packetwiseMinimum
  /-- Reciprocal-density algebraic identities. -/
  | reciprocalDensityIdentities
  /-- `RECIPROCAL-DENSITY-DUALITY45` as a research row. -/
  | reciprocalDensityDuality45
  /-- Affine-product pushforward and collision identity. -/
  | affineProductCollision
  /-- Affine-product (Cochrane–Shi type) modular energy. -/
  | affineProductEnergy45
  /-- Weighted `Ω` divisor-moment norm. -/
  | omegaWeightedDivisorMoment
  /-- Ordinary `Ω_H` `ℓ²` normalisation (distinct pin). -/
  | omegaOrdinaryL2
  /-- Complete Perron / nuclear normalisation. -/
  | perronNuclearNormalisation
  /-- The Archimedean dual factor. -/
  | archDualParameter
  /-- Outer Möbius sign at the dual level. -/
  | mobiusSign
  /-- `THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45` (historical). -/
  | singleCarrier45
  /-- `BRANCHI-ULTRANEAR-BEZOUTROW-CRITICALDENSITY-MOBIUSLEVEL45` (historical). -/
  | ultraNearCriticalDensityMobiusLevel45
  /-- The old scale-saturation face. -/
  | oldSaturationFace
  /-- Cross-packet two-axis architecture (retracted). -/
  | crossPacketTwoAxis
  /-- `THREEFACTOR-TRANSVERSE-BRANCHI-SIMULTANEOUSCRITICAL-DUALLEVEL-AFFINEPRODUCT-MOBIUS45`. -/
  | simultaneousCriticalMobius45
  /-- Level Type-I admissibility. -/
  | levelTypeI
  /-- Level Type-II admissibility (287-local). -/
  | levelTypeII
  /-- The transverse branch as a whole. -/
  | transverseBranch
  /-- The `b`-diagonal branch. -/
  | bDiagonal
  /-- The C0 branch. -/
  | c0
  /-- Erdős problem #287. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

open DualLevelNode

/-- The dual-level / simultaneous-critical ledger. -/
def dualLevelLedger : DualLevelNode → ResearchStatus
  | bezoutRowAffineAlgebra => kernelProved
  | bezoutThreeAxisFibre => kernelProved
  | bezoutThreeAxisFourier => kernelProved
  | largeGResidueCore => kernelProved
  | largeGWeightedRouter => conditionalSourcePin
  | allQAtomicGroupedCompiler => conditionalSourcePin
  | dualCRTSplit => kernelProved
  | additiveReciprocity => kernelProved
  | dualXiNormalForm => kernelProved
  | constantXiGcd => kernelProved
  | variableXiGcd => kernelProved
  | largeXiGcdRouter => conditionalSourcePin
  | dualFrequencyFibres => kernelProved
  | dualPairwiseFourier => kernelProved
  | packetwiseMinimum => kernelProved
  | reciprocalDensityIdentities => kernelProved
  | reciprocalDensityDuality45 => analyticBanked
  | affineProductCollision => kernelProved
  | affineProductEnergy45 => conditionalSourcePin
  | omegaWeightedDivisorMoment => conditionalSourcePin
  | omegaOrdinaryL2 => conditionalSourcePin
  | perronNuclearNormalisation => conditionalSourcePin
  | archDualParameter => conditionalSourcePin
  | mobiusSign => open_
  | singleCarrier45 => superseded
  | ultraNearCriticalDensityMobiusLevel45 => superseded
  | oldSaturationFace => superseded
  | crossPacketTwoAxis => retracted
  | simultaneousCriticalMobius45 => open_
  | levelTypeI => conditionalSourcePin
  | levelTypeII => strictReduction
  | transverseBranch => strictReduction
  | bDiagonal => open_
  | c0 => conditionalSourcePin
  | erdos287 => open_

/-! ## §2  Named status values -/

/-- `THREEFACTOR-TRANSVERSE-BEZOUTROW-THREEAXIS-UNITARY45`: the *finite* rows are kernel-proved. -/
def bezoutThreeAxisFiniteStatus : ResearchStatus := dualLevelLedger bezoutThreeAxisFourier

/-- `THREEFACTOR-TRANSVERSE-DUALLEVEL-RECIPROCITY45` (finite rows). -/
def dualLevelReciprocityFiniteStatus : ResearchStatus := dualLevelLedger dualCRTSplit

/-- `DUALLEVEL-PAIRWISEFOURIER45` (finite rows). -/
def dualPairwiseFourierFiniteStatus : ResearchStatus := dualLevelLedger dualPairwiseFourier

/-- `DUALLEVEL-XIGCD-ROUTER45`: formal status of the weighted tail. -/
def xiGcdRouterFormalStatus : ResearchStatus := dualLevelLedger largeXiGcdRouter

/-- `DUALLEVEL-AFFINEPRODUCT-ENERGY45`. -/
def affineProductEnergyStatus : ResearchStatus := dualLevelLedger affineProductEnergy45

/-- `RECIPROCAL-DENSITY-DUALITY45`. -/
def reciprocalDensityDualityStatus : ResearchStatus := dualLevelLedger reciprocalDensityDuality45

/-- The current first analytic residual. -/
def simultaneousCriticalStatus : ResearchStatus := dualLevelLedger simultaneousCriticalMobius45

/-- The `b`-diagonal row. -/
def bDiagonalStatus : ResearchStatus := dualLevelLedger bDiagonal

/-- The transverse branch row. -/
def transverseStatus : ResearchStatus := dualLevelLedger transverseBranch

/-- The C0 row. -/
def c0Status : ResearchStatus := dualLevelLedger c0

/-- Erdős #287. -/
def erdos287Status : ResearchStatus := dualLevelLedger erdos287

/-! ## §3  Ledger facts -/

/-- **`dualLevel_kernel_rows`.**  `LEAN_PROVED`.  Every `kernelProved` row of this delta is one of
the finite arithmetic / finite Fourier rows, and each of those really is backed by a theorem of
this repository (see §8 for the exact list). -/
theorem dualLevel_kernel_rows :
    dualLevelLedger bezoutRowAffineAlgebra = kernelProved ∧
    dualLevelLedger bezoutThreeAxisFibre = kernelProved ∧
    dualLevelLedger bezoutThreeAxisFourier = kernelProved ∧
    dualLevelLedger dualCRTSplit = kernelProved ∧
    dualLevelLedger additiveReciprocity = kernelProved ∧
    dualLevelLedger dualXiNormalForm = kernelProved ∧
    dualLevelLedger constantXiGcd = kernelProved ∧
    dualLevelLedger variableXiGcd = kernelProved ∧
    dualLevelLedger dualFrequencyFibres = kernelProved ∧
    dualLevelLedger dualPairwiseFourier = kernelProved ∧
    dualLevelLedger packetwiseMinimum = kernelProved ∧
    dualLevelLedger reciprocalDensityIdentities = kernelProved ∧
    dualLevelLedger affineProductCollision = kernelProved ∧
    dualLevelLedger largeGResidueCore = kernelProved := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`analytic_rows_are_not_kernel_rows`.**  `LEAN_PROVED`.  No analytic / source-pin / open row
is recorded as kernel-proved. -/
theorem analytic_rows_are_not_kernel_rows :
    reciprocalDensityDualityStatus ≠ kernelProved ∧
    affineProductEnergyStatus ≠ kernelProved ∧
    xiGcdRouterFormalStatus ≠ kernelProved ∧
    dualLevelLedger largeGWeightedRouter ≠ kernelProved ∧
    dualLevelLedger allQAtomicGroupedCompiler ≠ kernelProved ∧
    dualLevelLedger omegaWeightedDivisorMoment ≠ kernelProved ∧
    dualLevelLedger omegaOrdinaryL2 ≠ kernelProved ∧
    dualLevelLedger perronNuclearNormalisation ≠ kernelProved ∧
    dualLevelLedger archDualParameter ≠ kernelProved ∧
    dualLevelLedger mobiusSign ≠ kernelProved := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **`xiGcd_router_split`.**  `LEAN_PROVED`.  The `Ξ`-gcd router is split exactly as required:
the *arithmetic uniqueness* row is kernel-proved, while the *weighted tail* row is only a
conditional source pin.  Residue uniqueness alone never discharges the router. -/
theorem xiGcd_router_split :
    dualLevelLedger variableXiGcd = kernelProved ∧
    xiGcdRouterFormalStatus = conditionalSourcePin ∧
    xiGcdRouterFormalStatus ≠ kernelProved ∧
    dualLevelLedger variableXiGcd ≠ xiGcdRouterFormalStatus := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide +kernel

/-- **`omega_norms_are_separate_pins`.**  `LEAN_PROVED`.  The weighted `Ω` divisor-moment norm and
the ordinary `Ω_H` `ℓ²` normalisation are two **distinct** ledger nodes; neither is discharged.
The separating theorem is
`Erdos287.TransverseAffineProduct.omegaWeighted_not_implied_by_l2`. -/
theorem omega_norms_are_separate_pins :
    omegaWeightedDivisorMoment ≠ omegaOrdinaryL2 ∧
    dualLevelLedger omegaWeightedDivisorMoment = conditionalSourcePin ∧
    dualLevelLedger omegaOrdinaryL2 = conditionalSourcePin := by
  refine ⟨?_, rfl, rfl⟩
  decide +kernel

/-- **`simultaneousCritical_is_first_frontier`.**  `LEAN_PROVED`.  The current first analytic
residual is the simultaneous-critical dual-level affine-product Möbius row, and it is open. -/
theorem simultaneousCritical_is_first_frontier :
    simultaneousCriticalStatus = open_ ∧
    simultaneousCriticalStatus ≠ kernelProved ∧
    simultaneousCriticalStatus ≠ analyticBanked := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide +kernel

/-- **`superseded_frontiers_preserved`.**  `LEAN_PROVED`.  The two historical frontiers are marked
`superseded`, never `retracted` and never false; the old saturation face likewise. -/
theorem superseded_frontiers_preserved :
    dualLevelLedger singleCarrier45 = superseded ∧
    dualLevelLedger ultraNearCriticalDensityMobiusLevel45 = superseded ∧
    dualLevelLedger oldSaturationFace = superseded ∧
    dualLevelLedger singleCarrier45 ≠ retracted ∧
    dualLevelLedger ultraNearCriticalDensityMobiusLevel45 ≠ retracted ∧
    dualLevelLedger oldSaturationFace ≠ retracted := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **`crossPacket_two_axis_retracted`.**  `LEAN_PROVED`.  The cross-packet two-axis architecture
is recorded as retracted (structural failure: after division by `S S'` the numerator splits into
two separable one-variable reciprocal phases).  Only the retraction is recorded; no universal
impossibility theorem is asserted. -/
theorem crossPacket_two_axis_retracted :
    dualLevelLedger crossPacketTwoAxis = retracted ∧
    dualLevelLedger crossPacketTwoAxis ≠ kernelProved := by
  refine ⟨rfl, ?_⟩
  decide +kernel

/-- **`mobius_sign_remains_linear`.**  `LEAN_PROVED`.  The outer Möbius sign row stays `open`: no
cancellation theorem for it exists in this repository, and none is encoded in metadata. -/
theorem mobius_sign_remains_linear :
    dualLevelLedger mobiusSign = open_ ∧
    dualLevelLedger mobiusSign ≠ kernelProved ∧
    dualLevelLedger mobiusSign ≠ analyticBanked := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide +kernel

/-- **`level_typeI_typeII_status`.**  `LEAN_PROVED`.  Level Type-I is closed only on an explicit
source inequality (`conditionalSourcePin`); level Type-II is a strict reduction, with the
simultaneous-critical source class open.  Neither row is kernel-proved, and neither concerns any
downstream (non-287) Type-II statement. -/
theorem level_typeI_typeII_status :
    dualLevelLedger levelTypeI = conditionalSourcePin ∧
    dualLevelLedger levelTypeII = strictReduction ∧
    dualLevelLedger levelTypeI ≠ kernelProved ∧
    dualLevelLedger levelTypeII ≠ kernelProved := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide +kernel

/-- **`bdiagonal_untouched`.**  `LEAN_PROVED`.  The `b`-diagonal row stays open and distinct from
every transverse row; no dual-level theorem is credited to it. -/
theorem bdiagonal_untouched :
    bDiagonalStatus = open_ ∧ bDiagonalStatus ≠ kernelProved ∧
    bDiagonalStatus ≠ transverseStatus ∧
    bDiagonalStatus ≠ dualPairwiseFourierFiniteStatus := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **`erdos287_open_after_dualLevel`.**  `LEAN_PROVED`.  Erdős #287 remains open. -/
theorem erdos287_open_after_dualLevel :
    erdos287Status = open_ ∧ erdos287Status ≠ kernelProved ∧
    erdos287Status ≠ analyticBanked := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide +kernel

/-! ## §4  Boundary metadata of the new frontier

The research boundary constraints `D₀H₀ ≤ m L^C` and `Q ≈ R₀ L^{O(1)}` are recorded **only** as
labels; no asymptotic `~` is encoded as a theorem. -/

/-- Boundary constraints of the simultaneous-critical frontier.  Metadata labels only. -/
inductive SimultaneousCriticalBoundary
  /-- `D₀ H₀ ≤ m · L^C`. -/
  | oldDensityCritical
  /-- `Q ≈ R₀ · L^{O(1)}` on the boundary. -/
  | dualDensityCritical
  /-- One outer `μ(r₀)` sign remains linear. -/
  | linearMobiusSign
  deriving DecidableEq, Fintype, Repr

/-- **`boundary_constraints_are_metadata`.**  `LEAN_PROVED`.  The three boundary labels are
distinct labels and assert nothing: in particular no asymptotic relation is formalised. -/
theorem boundary_constraints_are_metadata :
    SimultaneousCriticalBoundary.oldDensityCritical ≠
      SimultaneousCriticalBoundary.dualDensityCritical ∧
    SimultaneousCriticalBoundary.dualDensityCritical ≠
      SimultaneousCriticalBoundary.linearMobiusSign ∧
    simultaneousCriticalStatus = open_ := by
  refine ⟨?_, ?_, rfl⟩ <;> decide +kernel

/-! ## §5  Movable numerator metadata

The true movable numerator coordinates of the Bézout row are `Δ₀` and `ℓ`.  The quotient
`(m · inverse(m mod r) - 1)/r` is **not** an independent source coordinate once `m`, `r` are
fixed.  This is recorded as metadata only — no philosophical theorem is encoded. -/

/-- Movable numerator coordinates of the Bézout row (metadata). -/
inductive MovableNumeratorCoordinate
  /-- `Δ₀`. -/
  | Delta0
  /-- `ℓ`. -/
  | ell
  deriving DecidableEq, Fintype, Repr

/-- Derived (non-independent) numerator quantities (metadata). -/
inductive DerivedNumeratorQuantity
  /-- `(m · inverse(m mod r) - 1)/r`, determined by `m` and `r`. -/
  | bezoutQuotient
  deriving DecidableEq, Fintype, Repr

/-- **`movable_coordinates_are_two`.**  `LEAN_PROVED`.  Exactly two movable coordinates are
recorded, and the Bézout quotient is filed as a derived quantity, not as a coordinate. -/
theorem movable_coordinates_are_two :
    (Finset.univ : Finset MovableNumeratorCoordinate).card = 2 ∧
    (Finset.univ : Finset DerivedNumeratorQuantity).card = 1 := by
  constructor <;> decide +kernel

/-! ## §6  Single-carrier absorption metadata -/

/-- Absorption record: the single-carrier atomic classification is absorbed by the three-axis
grouping.  Metadata only; the earlier structural content is **not** marked false. -/
inductive SingleCarrierAbsorption
  /-- The historical single-carrier frontier. -/
  | historicalFrontier
  /-- Its atomic classification, absorbed by the three-axis grouping. -/
  | absorbedByThreeAxisGrouping
  deriving DecidableEq, Fintype, Repr

/-- **`singleCarrier_absorbed_not_false`.**  `LEAN_PROVED`.  The single-carrier row is
`superseded` (as a *frontier*) and is not `retracted`: its structural content stands. -/
theorem singleCarrier_absorbed_not_false :
    dualLevelLedger singleCarrier45 = superseded ∧
    dualLevelLedger singleCarrier45 ≠ retracted ∧
    SingleCarrierAbsorption.historicalFrontier ≠
      SingleCarrierAbsorption.absorbedByThreeAxisGrouping := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide +kernel

/-! ## §7  Preservation of the earlier ledgers -/

open Erdos287.TransverseBezoutStatus in
/-- **`oneConductor_ledger_preserved`.**  `LEAN_PROVED`.  Every row of the previous
one-conductor / Bézout ledger is unchanged by this append-only delta. -/
theorem oneConductor_ledger_preserved :
    bezoutLedger BezoutNode.reducedConductorArithmetic = kernelProved ∧
    bezoutLedger BezoutNode.gammaCongruences = kernelProved ∧
    bezoutLedger BezoutNode.gammaReduction = kernelProved ∧
    bezoutLedger BezoutNode.qcUnitaryCompiler = kernelProved ∧
    bezoutLedger BezoutNode.oneConductorReciprocity45 = analyticBanked ∧
    bezoutLedger BezoutNode.criticalBezoutSingleCarrier45 = open_ ∧
    bezoutLedger BezoutNode.naiveSignlessPairDFT = retracted ∧
    bezoutLedger BezoutNode.transverseBranch = strictReduction ∧
    bezoutLedger BezoutNode.bDiagonal = open_ ∧
    bezoutLedger BezoutNode.erdos287 = open_ := by
  decide +kernel

/-- **`c0_ledger_preserved_after_dualLevel`.**  `LEAN_PROVED`.  The C0 unitary-Fourier ledger rows
are unchanged. -/
theorem c0_ledger_preserved_after_dualLevel :
    Erdos287.C0UnitaryFourierStatus.c0Status = conditionalSourcePin ∧
    Erdos287.C0UnitaryFourierStatus.omegaHStatus = conditionalSourcePin ∧
    Erdos287.C0UnitaryFourierStatus.erdos287Status = open_ := by
  decide +kernel

/-- **`singleCarrier_row_of_old_ledger_not_rewritten`.**  `LEAN_PROVED`.  In the *old* ledger the
single-carrier row still reads `open_`; it is marked `superseded` only in the *new* ledger, since
the first frontier has moved.  No historical row was rewritten. -/
theorem singleCarrier_row_of_old_ledger_not_rewritten :
    Erdos287.TransverseBezoutStatus.bezoutLedger
        Erdos287.TransverseBezoutStatus.BezoutNode.criticalBezoutSingleCarrier45 = open_ ∧
    dualLevelLedger singleCarrier45 = superseded := by
  refine ⟨rfl, rfl⟩

/-! ## §8  The theorems these rows refer to

* `bezoutRowAffineAlgebra` — `Erdos287.TransverseBezoutRow.BezoutRowData.gammaG_mod_m`,
  `gammaG_mod_m_inverse_free`, `gammaG_mod_r0`, `gammaG_affine_slope`,
  `gammaG_affine_injective_mod_r0`, `affine_residue_unique_of_unit_slope`.
* `largeGResidueCore` — `Erdos287.TransverseBezoutRow.affineGcd_divisor_residue_class`,
  `affineGcd_solution_set_subset_class`, `affineGcd_interval_count`.
* `bezoutThreeAxisFibre` — `Erdos287.TransverseBezoutThreeAxis.fG_mul_q`, `fG_fibre_q_congr`,
  `fG_fibre_ell_congr`, `box_fibre_card_le`.
* `bezoutThreeAxisFourier` — `Erdos287.TransverseBezoutThreeAxis.fiberAggregate_l2_le_maxFiber`,
  `fiberAggregate_sum`, `aggregatedFourier_bilinear_bound`, `bezoutRowThreeAxisFourier_bound`,
  `bezoutThreeAxis_contraction_identity`.
* `allQAtomicGroupedCompiler` — `transverseAllQAtomicGrouped_of_productEnergy` together with the
  explicit `GroupedQEnergyHypothesis` (proved non-automatic).
* `dualCRTSplit` — `Erdos287.TransverseDualLevel.transverseDualCRT_split_int`,
  `transverseDualCRT_split`, `addPhase_split`, `addPhase_congr`, `addPhase_norm`.
* `additiveReciprocity` — `additiveReciprocity_coprime`, `additiveReciprocity_phase`.
* `dualXiNormalForm` — `Cmqg_mod_m`, `Cmqg_mod_q`, `Xi_affine_slope`, `Xi_affine_slope_mod`,
  `DualReciprocityData`, `transverseDualLevelReciprocity`, `archDual_is_a_free_parameter`.
* `constantXiGcd` — `Erdos287.TransverseDualXi.dConst_dvd_Xi`, `M0Dual_mul_dConst`,
  `Xi0_mul_dConst`.
* `variableXiGcd` — `xiRed_coprime`, `xi_divisor_affine_residue_unique`,
  `constant_and_variable_xi_gcd_differ`.
* `largeXiGcdRouter` — the interface `XiGcdTailBound` with `xiGcdTailBound_not_automatic`.
* `dualFrequencyFibres` — `Erdos287.TransverseDualPairwise.fDual_r_unique`, `fDual_ell_unique`,
  `fDual_r_fibre_interval_count`, `fDual_ell_fibre_interval_count`, `card_le_of_fibre_fst/snd`.
* `dualPairwiseFourier` — `doubleAggregatedFourier_bound`, `dualPairwise_Delta_r_bound`,
  `dualPairwise_Delta_ell_bound`, `dualPairwise_ell_r_bound`,
  `dualPairwise_contraction_identity`.
* `packetwiseMinimum` — `dualPairwise_min_bound`, `dualPairwise_min_is_not_product`,
  `dualPairwise_min_of_two_counts`.
* `reciprocalDensityIdentities` — `Erdos287.ReciprocalDensityDuality.*`.
* `affineProductCollision` — `Erdos287.TransverseAffineProduct.affineProduct_pushforward`,
  `affineProduct_collision_iff`.
* `affineProductEnergy45` — the interface `AffineProductEnergyBound` and the conditional
  `dualAffineProductFourier_of_energy`.
* `omegaWeightedDivisorMoment` — the interface `OmegaWeightedDivisorMomentBound` and the
  separation theorem `omegaWeighted_not_implied_by_l2`. -/

end SimultaneousCriticalStatus
end Erdos287
