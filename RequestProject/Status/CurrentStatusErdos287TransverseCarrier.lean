import Mathlib
import RequestProject.Status.CurrentStatusErdos287C0UnitaryFourier
import RequestProject.CurrentProgramme.Erdos287TransverseCarrierInterface

/-!
# Append-only status layer — Erdős #287, transverse carrier factorisation

This module is **append-only**; the C0 unitary-Fourier ledger is re-checked, not edited.

What is formally available on the transverse side is exactly one finite theorem — the
two-carrier reciprocal unitary Fourier bound, valid for arbitrary `ℓ²` coefficients — and
nothing else.  In particular this repository does **not** encode:

```
E = e/a₁ and R = r₂/c₂ are both long;
E · R > m L^K;
every transverse packet has a usable two-carrier pair;
THREEFACTOR-TRANSVERSE-SINGLECARRIER-RESIDUAL45 as an exact fact.
```

Next exact research child:

```
THREEFACTOR-TRANSVERSE-CARRIERFACTORIZATION-PAIR-EXISTENCE45 : OPEN.
```

Parallel, untouched:

```
BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45 : OPEN.
```
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseCarrierStatus

open Erdos287.C0UnitaryFourierStatus
open ResearchStatus

/-! ## §1  Nodes -/

/-- Nodes of the transverse-carrier ledger. -/
inductive TransverseNode
  /-- The finite two-carrier reciprocal unitary Fourier mechanism. -/
  | twoCarrierUnitaryFourierMechanism
  /-- The observation that the finite theorem needs no pointwise `Ω_H` formula. -/
  | omegaHBlindFiniteTheorem
  /-- Atomic carrier factorisation of `Q_*^red`. -/
  | qStarRedCarrierFactorisation
  /-- Dependence of `B_*^red` on each carrier. -/
  | bStarRedCarrierDependence
  /-- Existence of two simultaneously long usable signless carriers. -/
  | twoLongCarrierExistence
  /-- Completeness of a single-carrier residual classification. -/
  | singleCarrierResidualCompleteness
  /-- `THREEFACTOR-TRANSVERSE-CARRIERFACTORIZATION-PAIR-EXISTENCE45`, the next exact child. -/
  | pairExistence45
  /-- `THREEFACTOR-TRANSVERSE-SINGLECARRIER-RESIDUAL45`: only a candidate child. -/
  | singleCarrierResidual45
  /-- `BDIAGONAL-AFFINEA-SURVIVING-VERTEX-RECT45`, parallel branch. -/
  | bdiagonalAffineASurvivingVertexRect45
  /-- The transverse branch as a whole. -/
  | transverseBranch
  deriving DecidableEq, Fintype, Repr

open TransverseNode

/-- The transverse-carrier ledger. -/
def transverseLedger : TransverseNode → ResearchStatus
  | twoCarrierUnitaryFourierMechanism => kernelProved
  | omegaHBlindFiniteTheorem => kernelProved
  | qStarRedCarrierFactorisation => open_
  | bStarRedCarrierDependence => open_
  | twoLongCarrierExistence => open_
  | singleCarrierResidualCompleteness => open_
  | pairExistence45 => open_
  | singleCarrierResidual45 => open_
  | bdiagonalAffineASurvivingVertexRect45 => open_
  | transverseBranch => strictReduction

/-- Status of the transverse branch as a whole: strictly reduced, still open. -/
def nextTransverseStatus : ResearchStatus := transverseLedger transverseBranch

/-! ## §2  Ledger facts -/

/-- **`only_finite_mechanism_is_kernelProved`.**  `LEAN_PROVED`.  On the transverse side only the
finite Fourier mechanism (and the `Ω_H`-blindness of that same theorem) is kernel-proved. -/
theorem only_finite_mechanism_is_kernelProved :
    ∀ n : TransverseNode, transverseLedger n = kernelProved →
      n = twoCarrierUnitaryFourierMechanism ∨ n = omegaHBlindFiniteTheorem := by
  decide +kernel

/-- **`carrier_factorisation_open`.**  `LEAN_PROVED`.  The atomic carrier factorisation, the
`B_*^red` dependence, the two-long-carrier existence and the single-carrier completeness are all
open, and none is kernel-proved. -/
theorem carrier_factorisation_open :
    transverseLedger qStarRedCarrierFactorisation = open_ ∧
    transverseLedger bStarRedCarrierDependence = open_ ∧
    transverseLedger twoLongCarrierExistence = open_ ∧
    transverseLedger singleCarrierResidualCompleteness = open_ ∧
    transverseLedger twoLongCarrierExistence ≠ kernelProved := by
  decide +kernel

/-- **`pair_existence_is_next_child`.**  `LEAN_PROVED`.  The next exact research child is
`THREEFACTOR-TRANSVERSE-CARRIERFACTORIZATION-PAIR-EXISTENCE45`, and it is open; the
single-carrier residual is *not* promoted ahead of it. -/
theorem pair_existence_is_next_child :
    transverseLedger pairExistence45 = open_ ∧
    transverseLedger singleCarrierResidual45 = open_ ∧
    transverseLedger singleCarrierResidual45 ≠ kernelProved ∧
    transverseLedger singleCarrierResidual45 ≠ analyticBanked := by
  decide +kernel

/-- **`bdiagonal_parallel_and_open`.**  `LEAN_PROVED`.  The parallel `b`-diagonal branch stays
open and is untouched by this delta. -/
theorem bdiagonal_parallel_and_open :
    transverseLedger bdiagonalAffineASurvivingVertexRect45 = open_ ∧
    transverseLedger bdiagonalAffineASurvivingVertexRect45 ≠ kernelProved ∧
    transverseLedger bdiagonalAffineASurvivingVertexRect45 ≠ analyticBanked := by
  decide +kernel

/-- **`transverse_branch_strictly_reduced`.**  `LEAN_PROVED`.  The transverse branch is strictly
reduced, not closed. -/
theorem transverse_branch_strictly_reduced :
    nextTransverseStatus = strictReduction ∧
    nextTransverseStatus ≠ kernelProved ∧ nextTransverseStatus ≠ analyticBanked := by
  decide +kernel

/-- **`no_double_spending`.**  `LEAN_PROVED`.  The C0 row and the transverse row are separate
ledger entries with different labels, and the parallel `b`-diagonal row is a third: no saving
recorded on one row is automatically credited to another. -/
theorem no_double_spending :
    c0Status = conditionalSourcePin ∧
    nextTransverseStatus = strictReduction ∧
    transverseLedger bdiagonalAffineASurvivingVertexRect45 = open_ ∧
    c0Status ≠ nextTransverseStatus ∧
    nextTransverseStatus ≠ transverseLedger bdiagonalAffineASurvivingVertexRect45 := by
  decide +kernel

/-- **`c0_ledger_still_preserved`.**  `LEAN_PROVED`.  The C0 unitary-Fourier rows are unchanged
by this append-only delta. -/
theorem c0_ledger_still_preserved :
    c0Status = conditionalSourcePin ∧
    omegaHStatus = conditionalSourcePin ∧
    completePerronNormalisationStatus = conditionalSourcePin ∧
    erdos287Status = open_ := by
  decide +kernel

/-! ## §3  The theorems these rows refer to

* `twoCarrierUnitaryFourierMechanism` —
  `Erdos287.ReciprocalUnitaryFourier.transverseTwoCarrierUnitaryFourier`,
  `Erdos287.TransverseCarrier.transverseTwoCarrier_bound_of_unitSupport`,
  `Erdos287.TransverseCarrier.transverseTwoCarrier_bound_with_fibre_weights`.
* `omegaHBlindFiniteTheorem` — the same theorems, which quantify over arbitrary coefficient
  vectors: no pointwise formula of `Ω_H` occurs in their statements, only `ℓ²` masses.  The
  transverse `E`-carrier is therefore *not analytically blocked by the formula of* `Ω_H`; it is
  conditional only on an explicit `Ω_H` `ℓ²` normalisation
  (`Erdos287.C0PhysicalNormalisation.OmegaHL2NormalisationHypothesis`).
* the four open rows are represented only by the unfilled fields of
  `Erdos287.TransverseCarrier.TransverseCarrierPacket` and by the predicate
  `UsableTwoCarrierPair`, proved neither automatic nor contradictory.

D4 routing (research metadata): any failure of the complete physical unit condition on
`C_Π = a_ρ b_ρ⁻¹ u_ρ` is routed to D4.  The formal repository contains only the arithmetic
firewall `Erdos287.BalancedBUnitaryFourier.coprime_product_all`; the routing itself is not
proved, since its source predicates are not formalised. -/

end TransverseCarrierStatus
end Erdos287
