import Mathlib
import RequestProject.Status.CurrentStatusErdos287TransverseCarrier
import RequestProject.CurrentProgramme.Erdos287TransverseDenseQCInterface

/-!
# Append-only status layer — Erdős #287, transverse one-conductor / critical Bézout frontier

This module is **append-only**.  The earlier C0 unitary-Fourier ledger and the earlier
transverse-carrier ledger are re-checked, not edited; `previous_transverse_ledger_preserved` and
`c0_ledger_still_preserved_after_oneConductor` record that their rows are unchanged.

```
C0:
    ANALYTICALLY CLOSED
    CONDITIONAL ON FORMAL NORMALISATION
    (source pin SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45, plus the complete
     Perron/nuclear normalisation).

EXACT PRODUCT COLLISION:   ANALYTICALLY CLOSED (research bank).
DOUBLE TYPE II:            ANALYTICALLY CLOSED (research bank).

THREEFACTOR-TRANSVERSE-ONECONDUCTOR-RECIPROCITY45 :  PASS  (analytic bank).
THREEFACTOR-TRANSVERSE-qC-UNITARYFOURIER45        :  PASS  (analytic bank).
THREEFACTOR-TRANSVERSE-DENSE-qC-COMPILER45        :  CLOSED ON ITS EXPLICIT HYPOTHESES.

FULL TRANSVERSE:  STRICTLY REDUCED / OPEN.

CURRENT FIRST ANALYTIC RESIDUAL:
    THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45 : OPEN.

SUPERSEDED AS FIRST FRONTIER (not deleted, not marked false):
    THREEFACTOR-TRANSVERSE-CARRIERFACTORIZATION-PAIR-EXISTENCE45.

PARALLEL:
    BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45 : OPEN / UNTOUCHED.

ERDOS287: OPEN.
```

`ResearchStatus` is metadata: **no value of it carries any implication of mathematical truth**.
The only `kernelProved` rows are the finite arithmetic theorems of this delta.

A research-status **firewall** is recorded in §4: the naive signless-pair DFT of the fused
`q_C · q_m` modulus is *retracted* as a source dictionary.  After full CRT fusion the numerator
carries cross-modulus inverse coefficients and does not in general reduce to
`Γ · inverse(E) · inverse(R)` with `Γ` fixed.  No universal non-equality theorem is asserted:
only the retraction is recorded.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseBezoutStatus

open Erdos287.C0UnitaryFourierStatus
open ResearchStatus

/-! ## §1  Nodes -/

/-- Nodes of the one-conductor / critical-Bézout ledger. -/
inductive BezoutNode
  /-- Reduced-conductor arithmetic (`q̄`, `R̂_P`, `Q_*`, `Q_*^red`). -/
  | reducedConductorArithmetic
  /-- One-conductor `Γ` congruences mod `m` and mod `r`. -/
  | gammaCongruences
  /-- `Γ` gcd normal form and the reduced coprime numerator. -/
  | gammaReduction
  /-- Instantiation of the banked reciprocal unitary Fourier theorem at `(m_P, Γ^red)`. -/
  | qcUnitaryCompiler
  /-- The `R`-carrier finite harmonic-square bound. -/
  | rCarrierHarmonicEnergy
  /-- `THREEFACTOR-TRANSVERSE-ONECONDUCTOR-RECIPROCITY45`. -/
  | oneConductorReciprocity45
  /-- `THREEFACTOR-TRANSVERSE-qC-UNITARYFOURIER45`. -/
  | qCUnitaryFourier45
  /-- `THREEFACTOR-TRANSVERSE-DENSE-qC-COMPILER45`. -/
  | denseQCCompiler45
  /-- `THREEFACTOR-TRANSVERSE-CRITICAL-BEZOUTNUMERATOR-SINGLECARRIER45`. -/
  | criticalBezoutSingleCarrier45
  /-- `THREEFACTOR-TRANSVERSE-CARRIERFACTORIZATION-PAIR-EXISTENCE45`, superseded as the first
  frontier (its carrier interfaces are **not** marked false). -/
  | carrierFactorizationPairExistence45
  /-- The critical (survivor) polytope. -/
  | criticalPolytope
  /-- Naive signless-pair DFT of the fused `q_C · q_m` modulus. -/
  | naiveSignlessPairDFT
  /-- Physical `Ω_H` `ℓ²` normalisation. -/
  | omegaHNormalisation
  /-- Complete Perron / nuclear normalisation. -/
  | perronNuclearNormalisation
  /-- Analytic source-length lower bounds. -/
  | sourceLengthLowerBounds
  /-- Physical product-energy comparisons. -/
  | productEnergyComparison
  /-- The C0 branch. -/
  | c0
  /-- Exact product collision branch. -/
  | exactProductCollision
  /-- Double Type-II branch. -/
  | doubleTypeII
  /-- The transverse branch as a whole. -/
  | transverseBranch
  /-- `BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45`. -/
  | bDiagonal
  /-- Erdős problem #287. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

open BezoutNode

/-- The one-conductor / critical-Bézout ledger. -/
def bezoutLedger : BezoutNode → ResearchStatus
  | reducedConductorArithmetic => kernelProved
  | gammaCongruences => kernelProved
  | gammaReduction => kernelProved
  | qcUnitaryCompiler => kernelProved
  | rCarrierHarmonicEnergy => kernelProved
  | oneConductorReciprocity45 => analyticBanked
  | qCUnitaryFourier45 => analyticBanked
  | denseQCCompiler45 => analyticBanked
  | criticalBezoutSingleCarrier45 => open_
  | carrierFactorizationPairExistence45 => superseded
  | criticalPolytope => open_
  | naiveSignlessPairDFT => retracted
  | omegaHNormalisation => conditionalSourcePin
  | perronNuclearNormalisation => conditionalSourcePin
  | sourceLengthLowerBounds => open_
  | productEnergyComparison => open_
  | c0 => conditionalSourcePin
  | exactProductCollision => analyticBanked
  | doubleTypeII => analyticBanked
  | transverseBranch => strictReduction
  | bDiagonal => open_
  | erdos287 => open_

/-! ## §2  Named status values (exactly as requested) -/

/-- `THREEFACTOR-TRANSVERSE-ONECONDUCTOR-RECIPROCITY45 : PASS` (analytic bank). -/
def threefactorTransverseOneConductorReciprocityStatus : ResearchStatus :=
  bezoutLedger oneConductorReciprocity45

/-- Status of the one-conductor reciprocity row. -/
def transverseOneConductorStatus : ResearchStatus := bezoutLedger oneConductorReciprocity45

/-- Status of the `q_C` unitary Fourier row. -/
def transverseQCUnitaryStatus : ResearchStatus := bezoutLedger qCUnitaryFourier45

/-- Status of the dense-`q_C` compiler row. -/
def transverseDenseQCStatus : ResearchStatus := bezoutLedger denseQCCompiler45

/-- Status of the critical Bézout-numerator single-carrier row: the current first analytic
frontier. -/
def transverseCriticalBezoutSingleCarrierStatus : ResearchStatus :=
  bezoutLedger criticalBezoutSingleCarrier45

/-- Status of the (now superseded) carrier-factorisation pair-existence row. -/
def carrierFactorizationPairExistenceStatus : ResearchStatus :=
  bezoutLedger carrierFactorizationPairExistence45

/-- Status of the critical (survivor) polytope: open. -/
def criticalPolytopeStatus : ResearchStatus := bezoutLedger criticalPolytope

/-- Status of the naive full-CRT signless-pair DFT: retracted. -/
def naiveFullCRTDFTStatus : ResearchStatus := bezoutLedger naiveSignlessPairDFT

/-- Status of the C0 branch in this ledger. -/
def c0Status : ResearchStatus := bezoutLedger c0

/-- Status of the exact-product collision branch. -/
def exactProductCollisionStatus : ResearchStatus := bezoutLedger exactProductCollision

/-- Status of the double Type-II branch. -/
def doubleTypeIIStatus : ResearchStatus := bezoutLedger doubleTypeII

/-- Status of the `b`-diagonal branch. -/
def bDiagonalStatus : ResearchStatus := bezoutLedger bDiagonal

/-- Status of the transverse branch as a whole. -/
def transverseStatus : ResearchStatus := bezoutLedger transverseBranch

/-- Status of Erdős #287. -/
def erdos287Status : ResearchStatus := bezoutLedger erdos287

/-! ## §3  Ledger facts -/

/-- **`new_kernel_rows`.**  `LEAN_PROVED`.  Exactly the five finite arithmetic rows of this
delta carry `kernelProved`, and no analytic row, source pin, open row or retracted row does. -/
theorem new_kernel_rows :
    (∀ n : BezoutNode, bezoutLedger n = kernelProved →
      n = reducedConductorArithmetic ∨ n = gammaCongruences ∨ n = gammaReduction ∨
      n = qcUnitaryCompiler ∨ n = rCarrierHarmonicEnergy) ∧
    bezoutLedger reducedConductorArithmetic = kernelProved ∧
    bezoutLedger gammaCongruences = kernelProved ∧
    bezoutLedger gammaReduction = kernelProved ∧
    bezoutLedger qcUnitaryCompiler = kernelProved ∧
    bezoutLedger rCarrierHarmonicEnergy = kernelProved := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **`transverse_bank_rows`.**  `LEAN_PROVED`.  The three banked transverse rows are recorded as
analytic bank entries, never as kernel-proved facts about the physical source. -/
theorem transverse_bank_rows :
    transverseOneConductorStatus = analyticBanked ∧
    transverseQCUnitaryStatus = analyticBanked ∧
    transverseDenseQCStatus = analyticBanked ∧
    transverseOneConductorStatus ≠ kernelProved ∧
    transverseQCUnitaryStatus ≠ kernelProved ∧
    transverseDenseQCStatus ≠ kernelProved := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **`oneConductor_status_label`.**  `LEAN_PROVED`.  The requested label
`threefactorTransverseOneConductorReciprocityStatus := analyticBanked`, and it does not encode
full transverse closure (the transverse branch stays `strictReduction`). -/
theorem oneConductor_status_label :
    threefactorTransverseOneConductorReciprocityStatus = analyticBanked ∧
    transverseStatus = strictReduction ∧
    transverseStatus ≠ kernelProved ∧ transverseStatus ≠ analyticBanked := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide +kernel

/-- **`criticalBezout_is_first_frontier`.**  `LEAN_PROVED`.  The current first analytic residual
is the critical Bézout-numerator single-carrier row, which is open; the older
carrier-factorisation pair-existence row is marked `superseded` (preserved, not deleted, and its
underlying carrier interfaces are not marked false). -/
theorem criticalBezout_is_first_frontier :
    transverseCriticalBezoutSingleCarrierStatus = open_ ∧
    transverseCriticalBezoutSingleCarrierStatus ≠ kernelProved ∧
    transverseCriticalBezoutSingleCarrierStatus ≠ analyticBanked ∧
    carrierFactorizationPairExistenceStatus = superseded ∧
    carrierFactorizationPairExistenceStatus ≠ retracted := by
  refine ⟨rfl, ?_, ?_, rfl, ?_⟩ <;> decide +kernel

/-- **`criticalPolytope_open`.**  `LEAN_PROVED`.  The critical (survivor) polytope is recorded as
open: no theorem asserts that a physical balanced configuration exists, and none asserts that the
single-carrier residual is empty. -/
theorem criticalPolytope_open :
    criticalPolytopeStatus = open_ ∧ criticalPolytopeStatus ≠ kernelProved ∧
    criticalPolytopeStatus ≠ analyticBanked := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide +kernel

/-! ## §4  The retracted naive full-CRT DFT -/

/-- **`naive_full_crt_dft_retracted`.**  `LEAN_PROVED`.  Research-status firewall: the naive
signless-pair DFT of the fused `q_C · q_m` modulus is retracted as a source dictionary and must
not be re-encoded.  Only the retraction is recorded; no universal non-equality theorem is
asserted. -/
theorem naive_full_crt_dft_retracted :
    naiveFullCRTDFTStatus = retracted ∧ naiveFullCRTDFTStatus ≠ kernelProved ∧
    naiveFullCRTDFTStatus ≠ analyticBanked := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide +kernel

/-! ## §5  Conditionality firewall -/

/-- **`conditionality_firewall`.**  `LEAN_PROVED`.  The physical `Ω_H` `ℓ²` normalisation, the
complete Perron/nuclear normalisation, the analytic source-length lower bounds and the physical
product-energy comparisons all remain explicit hypotheses/interfaces; none is kernel-proved. -/
theorem conditionality_firewall :
    bezoutLedger omegaHNormalisation = conditionalSourcePin ∧
    bezoutLedger perronNuclearNormalisation = conditionalSourcePin ∧
    bezoutLedger sourceLengthLowerBounds = open_ ∧
    bezoutLedger productEnergyComparison = open_ ∧
    bezoutLedger omegaHNormalisation ≠ kernelProved ∧
    bezoutLedger perronNuclearNormalisation ≠ kernelProved ∧
    bezoutLedger sourceLengthLowerBounds ≠ kernelProved ∧
    bezoutLedger productEnergyComparison ≠ kernelProved := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **`c0_still_conditional`.**  `LEAN_PROVED`.  C0 is recorded as analytically closed
*conditional on formal normalisation*: the row is `conditionalSourcePin`, never `kernelProved`
and never an unconditional bank entry. -/
theorem c0_still_conditional :
    c0Status = conditionalSourcePin ∧ c0Status ≠ kernelProved ∧ c0Status ≠ analyticBanked := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide +kernel

/-- **`analytic_branch_rows`.**  `LEAN_PROVED`.  The exact-product-collision and double Type-II
branches are analytic bank entries. -/
theorem analytic_branch_rows :
    exactProductCollisionStatus = analyticBanked ∧ doubleTypeIIStatus = analyticBanked ∧
    exactProductCollisionStatus ≠ kernelProved ∧ doubleTypeIIStatus ≠ kernelProved := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide +kernel

/-! ## §6  `b`-diagonal firewall, double-spending, preservation -/

/-- **`bdiagonal_firewall`.**  `LEAN_PROVED`.  The parallel `b`-diagonal row stays open and
untouched, is labelled differently from every transverse row, and no `q_C` Fourier row is
credited to it. -/
theorem bdiagonal_firewall :
    bDiagonalStatus = open_ ∧ bDiagonalStatus ≠ kernelProved ∧
    bDiagonalStatus ≠ analyticBanked ∧ bDiagonalStatus ≠ transverseStatus ∧
    bDiagonalStatus ≠ transverseQCUnitaryStatus := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **`no_double_spending_after_oneConductor`.**  `LEAN_PROVED`.  The C0 row, the transverse row
and the `b`-diagonal row remain three distinct ledger entries with three distinct labels. -/
theorem no_double_spending_after_oneConductor :
    c0Status = conditionalSourcePin ∧ transverseStatus = strictReduction ∧
    bDiagonalStatus = open_ ∧ c0Status ≠ transverseStatus ∧
    transverseStatus ≠ bDiagonalStatus ∧ c0Status ≠ bDiagonalStatus := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **`erdos287_still_open`.**  `LEAN_PROVED`.  Erdős #287 remains open. -/
theorem erdos287_still_open :
    erdos287Status = open_ ∧ erdos287Status ≠ kernelProved ∧
    erdos287Status ≠ analyticBanked := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide +kernel

open Erdos287.TransverseCarrierStatus in
/-- **`previous_transverse_ledger_preserved`.**  `LEAN_PROVED`.  The earlier transverse-carrier
ledger is unchanged by this append-only delta; in particular its `pairExistence45` row still
reads `open_` there (it is marked `superseded` only in the *new* ledger, as the first frontier
has moved). -/
theorem previous_transverse_ledger_preserved :
    transverseLedger TransverseNode.twoCarrierUnitaryFourierMechanism = kernelProved ∧
    transverseLedger TransverseNode.pairExistence45 = open_ ∧
    transverseLedger TransverseNode.bdiagonalAffineASurvivingVertexRect45 = open_ ∧
    nextTransverseStatus = strictReduction := by
  decide +kernel

/-- **`c0_ledger_still_preserved_after_oneConductor`.**  `LEAN_PROVED`.  The C0 unitary-Fourier
ledger rows are unchanged. -/
theorem c0_ledger_still_preserved_after_oneConductor :
    Erdos287.C0UnitaryFourierStatus.c0Status = conditionalSourcePin ∧
    Erdos287.C0UnitaryFourierStatus.omegaHStatus = conditionalSourcePin ∧
    Erdos287.C0UnitaryFourierStatus.completePerronNormalisationStatus = conditionalSourcePin ∧
    Erdos287.C0UnitaryFourierStatus.erdos287Status = open_ := by
  decide +kernel

/-! ## §7  Critical-survivor metadata (records only)

The current research conditions for a critical survivor are recorded verbatim as a datatype;
**no** exponent asymptotics and **no** physical nonemptiness claim is formalised. -/

/-- Schematic conditions under which a packet survives the dense-`q_C` route.  Metadata only. -/
inductive CriticalSurvivorCondition
  /-- `q < m_P · logarithmicMargin`. -/
  | denseFailsForQ
  /-- Every partition of `q` has one short side. -/
  | everyPartitionHasShortSide
  /-- The same, symmetrically, for `q'`. -/
  | symmetricForQPrime
  /-- `Q_*^red` lies in the long-conductor region. -/
  | qStarRedLong
  deriving DecidableEq, Fintype, Repr

/-- **`criticalSurvivor_conditions_are_metadata`.**  `LEAN_PROVED`.  The four conditions are
four distinct labels; the datatype asserts no inequality, no exponent asymptotics and no
nonemptiness. -/
theorem criticalSurvivor_conditions_are_metadata :
    CriticalSurvivorCondition.denseFailsForQ ≠
      CriticalSurvivorCondition.everyPartitionHasShortSide ∧
    CriticalSurvivorCondition.denseFailsForQ ≠ CriticalSurvivorCondition.symmetricForQPrime ∧
    CriticalSurvivorCondition.denseFailsForQ ≠ CriticalSurvivorCondition.qStarRedLong ∧
    criticalPolytopeStatus = open_ := by
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide +kernel

/-! ## §8  The theorems these rows refer to

* `reducedConductorArithmetic` —
  `Erdos287.TransverseReducedConductor.TransversePacket.qBar_mul_deltas`,
  `RHat_eq`, `RHat_pos`, `lcm_eq_mul_div_gcd`, `QStarRed_mul_dStar`,
  `QStarRed_exact_normal_form`, `QStarRed_eq_div`, `carrierClass_table`.
* `gammaCongruences` — `Erdos287.TransverseOneConductor.transverseGammaInt_modEq_m`,
  `transverseGammaInt_modEq_r`, `transverseGamma_mod_m`, `transverseGamma_mod_r`,
  `exists_inverse_of_coprime`, `reducedPhase_norm`, `reducedPhase_arithmetic_factor`.
* `gammaReduction` — `Erdos287.TransverseGammaReduction.transverseGamma_gcd_eq`,
  `transverseGammaRed_coprime`, `transverseGammaRed_isUnit`, and the bundled
  `OneConductorData.gcd_normal_form` / `gammaRed_coprime` / `gammaRed_isUnit`.
* `qcUnitaryCompiler` — `Erdos287.TransverseQCUnitary.inv_mul_factorisation_zmod`,
  `inv_mul_factorisation_zmod_nat`, `transverseQCUnitaryFourier_bound`,
  `transverseQCUnitaryFourier_l2_bound`, `transverseQCUnitary_omegaH_blind`,
  and the conditional `transverseQCGroupedUnitary_of_productEnergy`.  All of these *reuse* the
  banked Fourier theorem `reciprocalUnitaryFourier_bilinear_bound`; no second Fourier proof
  exists in this delta.
* `rCarrierHarmonicEnergy` —
  `Erdos287.TransverseReducedConductor.Rcarrier_harmonic_square_bound`.
* the dense-`q_C` row is represented by `Erdos287.TransverseDenseQC.DenseQCAdmissible` and the
  purely logical `denseQC_closed_of_unitary_margin`, whose margin hypothesis is proved
  non-automatic. -/

end TransverseBezoutStatus
end Erdos287
