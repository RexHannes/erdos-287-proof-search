import RequestProject.Erdos287.Anchored.BicyclicInterface
import RequestProject.Erdos287.Anchored.RouteBridge
import RequestProject.Erdos287.Direct.Reconciliation

/-!
# Anchored route — ledger, reconciliation and integrity

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Three programmes are now tracked, and they are **not merged**:

* **Route S** — the Source / FivePrime / Directed-Selberg / physical-`k = 1` programme
  (`Erdos287.Effectivity.latestEvidence`, cut `Erdos287.Effectivity.latestCutSet`);
* **Route D** — the Direct Reciprocal programme (`Erdos287.Direct.directEvidence`, cut
  `Erdos287.Direct.directCutSet`);
* **Route A** — the anchored / contact-graph *proof-side* programme of this namespace, with
  its own ledger `anchoredEvidence` and cut `anchoredCutSet`.

This file proves that the Route-S and Route-D ledgers, cut sets and the certified finite
frontier are unchanged, that no route discharges another, and that the anchored route adds
**no** finite exclusion and **no** claim about Erdős #287, which remains `OPEN`.
-/

open scoped BigOperators

namespace Erdos287
namespace Anchored

/-! ## A.25  The anchored ledger -/

/-- Evidence taxonomy of the anchored route. -/
inductive EvidenceAnchored
  /-- reconstructed in the Lean kernel here, with no unproved hypothesis -/
  | kernelProved
  /-- kernel-proved from explicitly named interface hypotheses -/
  | kernelConditional
  /-- open -/
  | openNode
  /-- refuted here -/
  | refuted
  deriving DecidableEq, Repr

/-- Only kernel-proved content counts as closed. -/
def EvidenceAnchored.isClosed : EvidenceAnchored → Bool
  | .kernelProved => true
  | _ => false

/-- The nodes of the anchored route. -/
inductive AnchoredNode
  /-- exact finite anchored reciprocal state and the reduced-numerator criterion -/
  | reciprocalState
  /-- the finite fingerprint criterion -/
  | fingerprint
  /-- the full prime-power layer equivalence -/
  | primePowerLayer
  /-- the local contact relation and its exact decision -/
  | contactRelation
  /-- exact leaf elimination / forest components -/
  | forestElimination
  /-- exact elimination of isolated cycle components -/
  | cycleElimination
  /-- excess bookkeeping and reduction to a leafless kernel -/
  | cycleRank
  /-- the bridge to the elementary top-layer package -/
  | topLayerBridge
  /-- global rejection of all branching kernels -/
  | branchingKernelRejection
  /-- the unconditional form of that rejection -/
  | unconditionalRejection
  /-- unrestricted Erdős #287 -/
  | erdos287
  deriving DecidableEq, Repr

/-- Evidence class of each anchored node. -/
def anchoredEvidence : AnchoredNode → EvidenceAnchored
  | .reciprocalState => .kernelProved
  | .fingerprint => .kernelProved
  | .primePowerLayer => .kernelProved
  | .contactRelation => .kernelProved
  | .forestElimination => .kernelProved
  | .cycleElimination => .kernelProved
  | .cycleRank => .kernelProved
  | .topLayerBridge => .kernelProved
  | .branchingKernelRejection => .openNode
  | .unconditionalRejection => .refuted
  | .erdos287 => .openNode

/-- The anchored cut: the single open global step, plus #287 itself. -/
def anchoredCutSet : List AnchoredNode := [.branchingKernelRejection, .erdos287]

/-- **`anchoredCut_all_open`.**  `KERNEL-PROVED` bookkeeping. -/
theorem anchoredCut_all_open :
    ∀ n ∈ anchoredCutSet, anchoredEvidence n = EvidenceAnchored.openNode := by
  intro n hn
  fin_cases hn <;> rfl

/-- **`anchored_erdos287_open`.**  `KERNEL-PROVED` bookkeeping.  Erdős #287 is `OPEN` here. -/
theorem anchored_erdos287_open : anchoredEvidence .erdos287 = EvidenceAnchored.openNode := rfl

/-! ## A.26  What the closed anchored nodes actually are -/

/-- **`reciprocalState_closed`.**  `KERNEL-PROVED`.  The exact reduced-numerator criterion,
for every prime. -/
theorem reciprocalState_closed :
    anchoredEvidence .reciprocalState = EvidenceAnchored.kernelProved ∧
      (∀ (p : ℕ) (_ : Fact p.Prime) (v : ℚ), v ≠ 0 →
        (1 ≤ padicValRat p v ↔ (p : ℤ) ∣ v.num)) :=
  ⟨rfl, fun p hp v hv => @one_le_padicValRat_iff_dvd_num p hp v hv⟩

/-- **`fingerprint_closed`.**  `KERNEL-PROVED`.  The exact fingerprint criterion. -/
theorem fingerprint_closed :
    anchoredEvidence .fingerprint = EvidenceAnchored.kernelProved ∧
      (∀ (p : ℕ) (_ : Fact p.Prime) (C P N : Finset ℕ),
        AnchoredFeasible p C P N ↔
          ((0 : ℚ) ∈ valueSet C P N ∨ (p : ℤ) ∣ fingerprint C P N)) :=
  ⟨rfl, fun p hp C P N => @anchoredFeasible_iff_fingerprint p hp C P N⟩

/-- **`primePowerLayer_closed`.**  `KERNEL-PROVED`.  The full prime-power layer equivalence,
with cofactors divisible by `p` retained. -/
theorem primePowerLayer_closed :
    anchoredEvidence .primePowerLayer = EvidenceAnchored.kernelProved ∧
      (∀ (p : ℕ) (_ : Fact p.Prime) (C E : Finset ℕ), E ⊆ C → (∀ c ∈ C, 0 < c) → E.Nonempty →
        (p ^ (padicValNat p (lcmOf C) + 1) ∣ cofactorNum C E ↔
          1 ≤ padicValRat p (recipSum E))) :=
  ⟨rfl, fun p hp _ _ hEC hC hne => @layer_primePower_iff p hp _ _ hEC hC hne⟩

/-- **`contactRelation_closed`.**  `KERNEL-PROVED`.  Exact decision of a finite contact
instance. -/
theorem contactRelation_closed :
    anchoredEvidence .contactRelation = EvidenceAnchored.kernelProved ∧
      (∀ I : ContactCSP, I.WellFormed → (I.Sat ↔ I.satB = true)) :=
  ⟨rfl, fun I hwf => I.sat_iff_satB hwf⟩

/-- **`forestElimination_closed`.**  `KERNEL-PROVED`.  Exact leaf elimination and the forest
decision. -/
theorem forestElimination_closed :
    anchoredEvidence .forestElimination = EvidenceAnchored.kernelProved ∧
      (∀ (I J : ContactCSP), ContactCSP.Peel I J → J.Edges = ∅ →
        (I.Sat ↔ ∀ v ∈ J.V, ∃ b : Bool, J.dom v b = true)) :=
  ⟨rfl, fun _ _ h hJ => ContactCSP.forest_decision h hJ⟩

/-- **`cycleElimination_closed`.**  `KERNEL-PROVED`.  Exact decision of an isolated cycle
component. -/
theorem cycleElimination_closed :
    anchoredEvidence .cycleElimination = EvidenceAnchored.kernelProved ∧
      (∀ (dom : ℕ → Bool → Bool) (rel : ℕ → ℕ → Bool → Bool → Bool) (x : ℕ) (l : List ℕ),
        (x :: l).Nodup →
          ((cycleCSP dom rel x l).Sat ↔ ∃ a b : Bool,
            transfer dom rel x l a b = true ∧ rel (lastOf x l) x b a = true)) :=
  ⟨rfl, fun dom rel x l hnd => cycleCSP_sat_iff dom rel x l hnd⟩

/-- **`cycleRank_closed`.**  `KERNEL-PROVED`.  Excess bookkeeping and the reduction of every
finite instance to a leafless branching kernel. -/
theorem cycleRank_closed :
    anchoredEvidence .cycleRank = EvidenceAnchored.kernelProved ∧
      (∀ I : ContactCSP, ∃ J, ContactCSP.Peel I J ∧ ContactCSP.Leafless J ∧
        (I.Sat ↔ J.Sat) ∧ J.excess = I.excess) := by
  refine ⟨rfl, fun I => ?_⟩
  obtain ⟨J, hJ, hJl⟩ := ContactCSP.exists_peel_to_leafless I
  exact ⟨J, hJ, hJl, hJ.sat_iff, hJ.excess_eq⟩

/-- **`topLayerBridge_closed`.**  `KERNEL-PROVED`.  The bridge to the elementary top-layer
package. -/
theorem topLayerBridge_closed :
    anchoredEvidence .topLayerBridge = EvidenceAnchored.kernelProved ∧
      (∀ (A : Finset ℕ) (p : ℕ), p.Prime → (∀ a ∈ A, 0 < a) →
        (∑ a ∈ A, (1 : ℚ) / a = 1) → 1 ≤ topExp A p →
        AnchoredFeasible p (topCofactors A p) (topCofactors A p) ∅) :=
  ⟨rfl, fun _ _ hp hpos hsum he => topLayer_anchoredFeasible hp hpos hsum he⟩

/-- **`unconditionalRejection_refuted`.**  `KERNEL-PROVED`.  The unconditional global
rejection of branching kernels is false. -/
theorem unconditionalRejection_refuted :
    anchoredEvidence .unconditionalRejection = EvidenceAnchored.refuted ∧
      ¬ BranchingKernelRejection (fun _ => True) :=
  ⟨rfl, branchingKernelRejection_unconditional_false⟩

/-! ## A.27  Reconciliation with the existing routes -/

/-- **`routeS_and_routeD_preserved`.**  `KERNEL-PROVED`.  The Route-S and Route-D ledgers and
cut sets are unchanged by this namespace. -/
theorem routeS_and_routeD_preserved :
    Effectivity.latestEvidence .erdos287 = Effectivity.EvidenceLatest.openNode ∧
    Effectivity.latestEvidence .finiteCeilingHere = Effectivity.EvidenceLatest.kernelProved ∧
    Effectivity.latestEvidence .finiteCeilingU2 =
      Effectivity.EvidenceLatest.pendingExternalImport ∧
    Direct.directEvidence .erdos287 = Direct.EvidenceDirect.openNode ∧
    Direct.directEvidence .exactSignedAbsorber = Direct.EvidenceDirect.openNode ∧
    (∀ n ∈ Direct.directCutSet, Direct.directEvidence n = Direct.EvidenceDirect.openNode) :=
  ⟨rfl, rfl, rfl, rfl, rfl, Direct.directCut_all_open⟩

/-- **`routes_independent`.**  `KERNEL-PROVED`.  No route discharges another: the cut nodes of
all three routes are simultaneously open. -/
theorem routes_independent :
    (∀ n ∈ Direct.directCutSet, Direct.directEvidence n = Direct.EvidenceDirect.openNode) ∧
    (∀ n ∈ anchoredCutSet, anchoredEvidence n = EvidenceAnchored.openNode) ∧
    Effectivity.latestEvidence .erdos287 = Effectivity.EvidenceLatest.openNode :=
  ⟨Direct.directCut_all_open, anchoredCut_all_open, rfl⟩

/-- **`anchored_finite_frontier_unchanged`.**  `KERNEL-PROVED`.  The certified finite frontier
is exactly the existing ceiling `67108856338751594`, with `U2` still pending; the anchored
route adds no finite exclusion. -/
theorem anchored_finite_frontier_unchanged :
    (∀ {A : Finset ℕ} (h : Erdos287Counterexample A),
        A.max' h.nonempty ≤ extendedCeiling → False) ∧
      extendedCeiling = 67108856338751594 ∧
      extendedCeiling < Effectivity.U2 ∧
      Effectivity.latestEvidence .finiteCeilingU2 =
        Effectivity.EvidenceLatest.pendingExternalImport :=
  Direct.finite_frontier_integrity

/-- **`anchored_open_frontier`.**  `KERNEL-PROVED`.  No open anchored node is tagged closed,
and the global branching-kernel rejection is not inhabited here: the only statement about it
proved in this namespace is the refutation of its unconditional form. -/
theorem anchored_open_frontier :
    (∀ n ∈ anchoredCutSet, (anchoredEvidence n).isClosed = false) ∧
      anchoredEvidence .branchingKernelRejection = EvidenceAnchored.openNode ∧
      ¬ BranchingKernelRejection (fun _ => True) := by
  refine ⟨?_, rfl, branchingKernelRejection_unconditional_false⟩
  intro n hn
  fin_cases hn <;> rfl

end Anchored
end Erdos287
