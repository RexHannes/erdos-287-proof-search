import Mathlib
import RequestProject.Erdos287.CurrentStatusEffectivityFrontierAudit
import RequestProject.Erdos287.FivePrimeSourceGeometry
import RequestProject.Erdos287.DirectedSelbergFiniteAlgebra
import RequestProject.Erdos287.HighXConsumerLedger
import RequestProject.Erdos287.PhysicalK1Owner

/-!
# Erdős #287 — authoritative current status (§69)

INTERNAL #287 EFFECTIVITY PROGRAMME ONLY.
**Erdős #287 is `OPEN` here and is not claimed.**

This is the current aggregator.  It extends — and does not rewrite — every earlier status
module (`CurrentStatusEffectivityBoundedConductor`, `CurrentStatusEffectivityEarly4490`,
`CurrentStatusEffectivityFrontierAudit`).  All banked layers keep their statements and their
evidence classes; the refuted propositions of §62 stay refuted and are **not** reused as
hypotheses anywhere in §65–§68.

It exposes:

* the finite theorem status and the `U2` integration status;
* the source/capacity status (five-prime `+6` geometry, directed Selberg finite algebra,
  the conditional `T_box` bound, the high-`X` consumer ledger);
* the corrected quantitative `k = 1` owner;
* the classification of every remaining analytic owner;
* the dependency DAG and the current **minimal open cut set**.

## Evidence taxonomy

`EvidenceLatest` distinguishes exactly the nine statuses used by the programme, including
`pendingExternalImport` for a result that exists elsewhere but is not supplied here.  An
analytic assumption is never tagged `kernelProved` merely because its deterministic consumer
has been formalised: the conditional bridges of §66–§68 are tagged `conditionalAnalytic`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Effectivity

/-! ## §69.1  Checkpoint and taxonomy -/

/-- The checkpoint of this synchronisation. -/
def latestCheckpoint : Checkpoint :=
  { date := "2026-09-10", version := "SOURCE_CAPACITY_LATEST_v1" }

/-- **`latest_checkpoint_tag`.**  `KERNEL-PROVED`. -/
theorem latest_checkpoint_tag :
    latestCheckpoint.date = "2026-09-10" ∧
      latestCheckpoint.version = "SOURCE_CAPACITY_LATEST_v1" := ⟨rfl, rfl⟩

/-- The evidence taxonomy in force at this checkpoint. -/
inductive EvidenceLatest
  /-- reconstructed in the Lean kernel in this repository -/
  | kernelProved
  /-- backed by a checked finite certificate/data object -/
  | certificateBacked
  /-- quoted external analytic input, not formally reconstructed -/
  | externalAnalytic
  /-- proved only under explicitly stated analytic hypotheses -/
  | conditionalAnalytic
  /-- open -/
  | openNode
  /-- refuted -/
  | falseClaim
  /-- a method retired because it cannot close its target -/
  | retiredNonclosing
  /-- correct but no longer the current root coordinate -/
  | superseded
  /-- proved in a separate project, not supplied to this repository -/
  | pendingExternalImport
  deriving DecidableEq, Repr

/-- Evidence classes that count as *closed* for bookkeeping purposes. -/
def EvidenceLatest.isClosed : EvidenceLatest → Bool
  | .kernelProved => true
  | .certificateBacked => true
  | _ => false

/-! ## §69.2  Nodes -/

/-- The nodes tracked at this checkpoint. -/
inductive LatestNode
  /-- the finite exclusion actually kernel-proved here -/
  | finiteCeilingHere
  /-- the separately announced finite exclusion up to `U2` -/
  | finiteCeilingU2
  /-- the five-prime one-low/four-high `+6` source geometry -/
  | fivePrimeSourceGeometry
  /-- unique factorisation in disjoint prime boxes -/
  | disjointPrimeBoxes
  /-- the finite algebra of the directed Selberg sieve -/
  | selbergFiniteAlgebra
  /-- the `T_box` capacity bound `6.3e-7 · X/log X` -/
  | tBoxCapacityBound
  /-- the high-`X` consumer ledger arithmetic -/
  | highXLedgerArithmetic
  /-- affordability of the `2.1e-6 · B_prime` allocation -/
  | boxAllocationAffordability
  /-- the corrected quantitative physical `k = 1` owner -/
  | physicalK1Quantitative
  /-- the refuted fixed-conductor character bound -/
  | fixedConductorCharacterBound
  /-- the refuted pointwise bounded-conductor `k = 1` target -/
  | pointwiseK1Target
  /-- the qualitative centred target -/
  | centredK1Qualitative
  /-- `Ω(k) = 2` -/
  | omegaTwo
  /-- `Ω(k) = 1` -/
  | omegaOne
  /-- the EARLY_4490 residual -/
  | early4490Residual
  /-- proper gamma over the full slab -/
  | properGamma
  /-- `S_live` -/
  | sLive
  /-- `R_012` -/
  | r012
  /-- the signed floor -/
  | signedFloor
  /-- the final splice -/
  | finalSplice
  /-- unrestricted Erdős #287 -/
  | erdos287
  deriving DecidableEq, Repr

/-- Evidence class of each node at this checkpoint. -/
def latestEvidence : LatestNode → EvidenceLatest
  | .finiteCeilingHere => .kernelProved
  | .finiteCeilingU2 => .pendingExternalImport
  | .fivePrimeSourceGeometry => .kernelProved
  | .disjointPrimeBoxes => .kernelProved
  | .selbergFiniteAlgebra => .kernelProved
  | .tBoxCapacityBound => .conditionalAnalytic
  | .highXLedgerArithmetic => .kernelProved
  | .boxAllocationAffordability => .openNode
  | .physicalK1Quantitative => .openNode
  | .fixedConductorCharacterBound => .falseClaim
  | .pointwiseK1Target => .falseClaim
  | .centredK1Qualitative => .retiredNonclosing
  | .omegaTwo => .openNode
  | .omegaOne => .openNode
  | .early4490Residual => .openNode
  | .properGamma => .openNode
  | .sLive => .openNode
  | .r012 => .openNode
  | .signedFloor => .openNode
  | .finalSplice => .openNode
  | .erdos287 => .openNode

/-- **`erdos287_open`.**  `KERNEL-PROVED` bookkeeping.  Erdős #287 is recorded open. -/
theorem erdos287_open : latestEvidence .erdos287 = EvidenceLatest.openNode := rfl

/-! ## §69.3  What is kernel-proved at this checkpoint -/

/-- **`fivePrime_geometry_kernel_proved`.**  `KERNEL-PROVED`.  The exact `+6` cell, its
separation cost, its representation exactness and the necessity of the balanced chamber. -/
theorem fivePrime_geometry_kernel_proved :
    SourceGeometry.H SourceGeometry.plusSixCell SourceGeometry.plusSixDelta
        SourceGeometry.plusSixDelta' = 6 ∧
      SourceGeometry.separationCost SourceGeometry.plusSixCell SourceGeometry.plusSixDelta
        SourceGeometry.plusSixDelta' = 6 ∧
      (0 < SourceGeometry.N1 SourceGeometry.straddleCell SourceGeometry.plusSixDelta
          SourceGeometry.plusSixDelta' ∧
        0 < SourceGeometry.N2 SourceGeometry.straddleCell SourceGeometry.plusSixDelta) ∧
      latestEvidence .fivePrimeSourceGeometry = EvidenceLatest.kernelProved :=
  ⟨SourceGeometry.plusSix_cell_H, SourceGeometry.plusSix_separationCost,
    SourceGeometry.straddle_witness, rfl⟩

/-- **`selberg_algebra_kernel_proved`.**  `KERNEL-PROVED`.  The finite Selberg optimum is the
capacity, and the capacity is monotone. -/
theorem selberg_algebra_kernel_proved {D : Finset ℕ} (S : DirectedSelberg.SelbergData D) :
    DirectedSelberg.quadraticForm S (DirectedSelberg.optimalY S) = DirectedSelberg.capacity S ∧
      latestEvidence .selbergFiniteAlgebra = EvidenceLatest.kernelProved :=
  ⟨DirectedSelberg.quadraticForm_optimal S, rfl⟩

/-- **`tBox_bound_is_conditional`.**  `KERNEL-PROVED` bookkeeping.  The `T_box` bound is a
*deterministic bridge*: it is proved only from its explicit analytic inputs (a capacity input
and a capacity lower bound), and is therefore tagged `conditionalAnalytic`, never
`kernelProved`. -/
theorem tBox_bound_is_conditional :
    latestEvidence .tBoxCapacityBound = EvidenceLatest.conditionalAnalytic ∧
      (∀ (T A Gval W : ℝ), 0 ≤ W → |T| ≤ 6 * A → A ≤ W / Gval → (9523810 : ℝ) ≤ Gval →
        |T| ≤ (63 / 10 ^ 8 : ℝ) * W) :=
  ⟨rfl, fun T A Gval W hW h1 h2 h3 => DirectedSelberg.T_box_bound_of_capacity hW h1 h2 h3⟩

/-- **`allocation_affordability_open`.**  `KERNEL-PROVED`.  The affordability of the
`2.1·10⁻⁶ · B_prime` allocation is undecided in this repository: admissible ledgers exist on
both sides, and the historical `10⁻¹¹` early-slab budget is far too small to be reused. -/
theorem allocation_affordability_open :
    latestEvidence .boxAllocationAffordability = EvidenceLatest.openNode ∧
      (HighX.Admissible HighX.generousLedger ∧
        HighX.Fits HighX.generousLedger HighX.boxAllocationRequest) ∧
      (HighX.Admissible HighX.tightLedger ∧
        ¬ HighX.Fits HighX.tightLedger HighX.boxAllocationRequest) ∧
      ¬ (HighX.boxAllocationRequest ≤ (1 / 10 ^ 11 : ℚ)) :=
  ⟨rfl, HighX.allocation_verdict_undecided.1, HighX.allocation_verdict_undecided.2,
    HighX.early_slab_budget_too_small⟩

/-! ## §69.4  The corrected `k = 1` owner and the retirement of the refuted ones -/

/-- **`k1_owner_replacement`.**  `KERNEL-PROVED`.  The three refuted propositions remain
refuted for every budget; the corrected owner is a different, *quantitative* proposition,
satisfiable for the explicit trivial constant, so its content is the smallness of the
budget.  The old propositions are permanently retired: they are not hypotheses of the new
owner and no identically named weaker statement replaces them. -/
theorem k1_owner_replacement (b : ℚ) :
    (¬ FixedConductorCharacterBound b ∧ ¬ FixedConductorCharacterMeanBound b ∧
        ¬ BoundedConductorK1Target b) ∧
      PhysicalK1Budget physicalK1TrivialBudget ∧
      latestEvidence .fixedConductorCharacterBound = EvidenceLatest.falseClaim ∧
      latestEvidence .pointwiseK1Target = EvidenceLatest.falseClaim ∧
      latestEvidence .centredK1Qualitative = EvidenceLatest.retiredNonclosing ∧
      latestEvidence .physicalK1Quantitative = EvidenceLatest.openNode :=
  ⟨refuted_targets_not_reused b, exists_physicalK1_budget, rfl, rfl, rfl, rfl⟩

/-- **`k1_density_obstruction_neutralised`.**  `KERNEL-PROVED`.  The long-window density
witness that refuted the pointwise target is annihilated by the correct centring, so the
corrected owner is not refuted by the banked obstruction. -/
theorem k1_density_obstruction_neutralised (n : ℕ) :
    centredWeighted (fun _ => 1) 0 ((bigPeriod : ℤ) * (n : ℤ)) 1 = 0 :=
  centredWeighted_full_period_vanishes n

/-- **`k1_open_content_is_nonconstant_weights`.**  `KERNEL-PROVED`.  The constant-weight case
of the corrected owner is closed with the explicit `X`-independent constant `centredBudget`
(§68.6), and the owner is split over conductors by `physicalK1_of_perConductor`.  What stays
open is therefore precisely the per-conductor bound for the *non-constant* true source
weights. -/
theorem k1_open_content_is_nonconstant_weights (X : ℕ) (A B z : ℤ) (hX : 1 ≤ X)
    (hwin : PhysicalWindow X A B) :
    |centredWeighted (fun _ => 1) A B z| ≤ centredBudget * (X : ℚ) ∧
      latestEvidence .physicalK1Quantitative = EvidenceLatest.openNode :=
  ⟨constantWeight_physicalK1 X A B z hX hwin, rfl⟩

/-! ## §69.5  The finite side and the `U2` reconciliation -/

/-- The announced separate finite ceiling `U2`. -/
def U2 : ℕ := 3739298103962937078961175187719640178760086558841160733818922

/-- **`u2_reconciliation_pending`.**  `KERNEL-PROVED` bookkeeping.  The `U2` project is **not**
supplied to this repository: no theorem, certificate or datum for it is present, so its status
is `pendingExternalImport`.  What *is* kernel-proved here is the strictly smaller ceiling
`extendedCeiling`, and `extendedCeiling < U2`, so nothing here implies the `U2` statement. -/
theorem u2_reconciliation_pending :
    latestEvidence .finiteCeilingU2 = EvidenceLatest.pendingExternalImport ∧
      latestEvidence .finiteCeilingHere = EvidenceLatest.kernelProved ∧
      extendedCeiling < U2 := by
  refine ⟨rfl, rfl, ?_⟩
  rw [extendedCeiling, U2]
  norm_num

/-- **`finite_ceiling_here`.**  `KERNEL-PROVED`.  The finite exclusion available in this
repository, restated at this checkpoint (statement unchanged from its ancestor). -/
theorem finite_ceiling_here {A : Finset ℕ} (h : Erdos287Counterexample A)
    (hM : A.max' h.nonempty ≤ extendedCeiling) : False :=
  finite_ceiling_kernel_proved h hM

/-! ## §69.6  The dependency DAG and the minimal open cut set -/

/-- The recorded prerequisites of each node (the edges of the dependency DAG). -/
def latestDeps : LatestNode → List LatestNode
  | .boxAllocationAffordability =>
      [.fivePrimeSourceGeometry, .selbergFiniteAlgebra, .highXLedgerArithmetic]
  | .physicalK1Quantitative => [.highXLedgerArithmetic]
  | .tBoxCapacityBound => [.fivePrimeSourceGeometry, .selbergFiniteAlgebra]
  | .erdos287 =>
      [.finiteCeilingHere, .physicalK1Quantitative, .boxAllocationAffordability, .omegaTwo, .omegaOne, .early4490Residual,
        .properGamma, .sLive, .r012, .signedFloor, .finalSplice]
  | _ => []

/-- The **current minimal open cut set**: the open propositions whose proof is still required.
Nodes that are merely historical, refuted or already closed are excluded. -/
def latestCutSet : List LatestNode :=
  [.physicalK1Quantitative, .boxAllocationAffordability, .omegaTwo, .omegaOne,
    .early4490Residual, .properGamma, .sLive, .r012, .signedFloor, .finalSplice]

/-- **`cutSet_all_open`.**  `KERNEL-PROVED`.  Every cut-set node is open. -/
theorem cutSet_all_open : ∀ n ∈ latestCutSet, latestEvidence n = EvidenceLatest.openNode := by
  intro n hn
  fin_cases hn <;> rfl

/-- **`cutSet_prerequisites_closed`.**  `KERNEL-PROVED`.  The cut set is *minimal* in the
recorded DAG: every prerequisite of every cut-set node is already closed, so no cut-set entry
is waiting on another one. -/
theorem cutSet_prerequisites_closed :
    ∀ n ∈ latestCutSet, ∀ m ∈ latestDeps n, (latestEvidence m).isClosed = true := by
  intro n hn
  fin_cases hn <;> intro m hm <;> fin_cases hm <;> rfl

/-- **`erdos287_needs_cutSet`.**  `KERNEL-PROVED`.  Erdős #287 depends on every cut-set node
(plus the finite ceiling, which is closed). -/
theorem erdos287_needs_cutSet : ∀ n ∈ latestCutSet, n ∈ latestDeps .erdos287 := by
  intro n hn
  fin_cases hn <;> simp [latestDeps]

/-- **`latest_open_frontier`.**  `KERNEL-PROVED`.  No open, refuted or retired node is tagged
closed at this checkpoint. -/
theorem latest_open_frontier :
    (∀ n ∈ latestCutSet, (latestEvidence n).isClosed = false) ∧
      (latestEvidence .erdos287).isClosed = false ∧
      (latestEvidence .fixedConductorCharacterBound).isClosed = false ∧
      (latestEvidence .pointwiseK1Target).isClosed = false ∧
      (latestEvidence .centredK1Qualitative).isClosed = false ∧
      (latestEvidence .tBoxCapacityBound).isClosed = false ∧
      (latestEvidence .finiteCeilingU2).isClosed = false := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro n hn
  fin_cases hn <;> rfl

/-- **`banked_layers_preserved_latest`.**  `KERNEL-PROVED`.  The ancestor banks keep their evidence
classes: this checkpoint adds nodes and never rewrites an earlier one. -/
theorem banked_layers_preserved_latest :
    boundedConductorEvidence .early4490BankAncestor = EvidenceCurrent.certificateBacked ∧
      boundedConductorEvidence .smallEllLocalMean = EvidenceCurrent.kernelProved ∧
      boundedConductorEvidence .crtAtomBound = EvidenceCurrent.kernelProved ∧
      boundedConductorEvidence .loopCancellationSmallEll = EvidenceCurrent.kernelProved ∧
      frontierAuditEvidence .boundedConductorK1Target = EvidenceCurrent.falseClaim :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## §69.7  Axiom audit -/

#print axioms Erdos287.SourceGeometry.plusSix_cell_H
#print axioms Erdos287.SourceGeometry.signSeparation_balanced
#print axioms Erdos287.SourceGeometry.H_mem_balanced
#print axioms Erdos287.SourceGeometry.straddle_witness
#print axioms Erdos287.SourceGeometry.plusSix_representation_exact
#print axioms Erdos287.SourceGeometry.fivePrimeBox_unique_factorisation
#print axioms Erdos287.DirectedSelberg.quadraticForm_ge_inv_capacity
#print axioms Erdos287.DirectedSelberg.quadraticForm_optimal
#print axioms Erdos287.DirectedSelberg.capacity_antitone
#print axioms Erdos287.DirectedSelberg.T_box_bound_of_capacity
#print axioms Erdos287.DirectedSelberg.T_box_ratio_bound
#print axioms Erdos287.HighX.allocation_verdict_undecided
#print axioms Erdos287.HighX.early_slab_budget_too_small
#print axioms Erdos287.HighX.cheap_requires_affordable
#print axioms Erdos287.Effectivity.centredWeighted_full_period_vanishes
#print axioms Erdos287.Effectivity.exists_physicalK1_budget
#print axioms Erdos287.Effectivity.physicalK1_consumer_bound
#print axioms Erdos287.Effectivity.k1_owner_replacement
#print axioms Erdos287.Effectivity.physicalK1_of_perConductor
#print axioms Erdos287.Effectivity.constantWeight_physicalK1
#print axioms Erdos287.Effectivity.k1_open_content_is_nonconstant_weights
#print axioms Erdos287.Effectivity.u2_reconciliation_pending
#print axioms Erdos287.Effectivity.cutSet_prerequisites_closed
#print axioms Erdos287.Effectivity.latest_open_frontier

end Effectivity
end Erdos287
