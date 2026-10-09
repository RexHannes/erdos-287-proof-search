import RequestProject.Erdos287.AnchoredV2.RouteBridge
import RequestProject.Erdos287.AnchoredV2.FeedbackEdge
import RequestProject.Erdos287.AnchoredV2.CactusMessage
import RequestProject.Erdos287.AnchoredV2.ThetaFirewall
import RequestProject.Erdos287.AnchoredV2.FiniteExtension
import RequestProject.Erdos287.Anchored.Reconciliation

/-!
# Anchored V2 — ledger, reconciliation and integrity

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Four ledgers are now tracked and are **not merged**:

* **Route S** — the Source / FivePrime / Directed-Selberg / physical-`k = 1` programme;
* **Route D** — the Direct Reciprocal programme;
* **Anchored V1** — the anchored / contact-graph programme, with its open owner
  `Erdos287.Anchored.BranchingKernelRejection`;
* **Anchored V2** — this namespace.

This file records the Anchored V2 ledger, re-checks that the Route-S, Route-D and Anchored-V1
ledgers, cut sets and the certified finite frontier are **unchanged and not extended**, and
records which old owner is *refined* by the new certificate owners.  The Anchored V1 global
branching owner is **not deleted**: it is kept, together with the proved implications

`UniformNegativeCapacity → BranchingKernelRejection`,
`UniformLevel2Rejection → BranchingKernelRejection`,

which are the only formal relations established between them.
-/

open scoped BigOperators

namespace Erdos287
namespace AnchoredV2

open Erdos287.Anchored
open Erdos287.Anchored.ContactCSP

/-- Evidence taxonomy of the Anchored V2 route. -/
inductive EvidenceV2
  /-- reconstructed in the Lean kernel here, with no unproved hypothesis -/
  | kernelProved
  /-- kernel-proved from explicitly named interface hypotheses (an owner) -/
  | kernelConditional
  /-- open -/
  | openNode
  /-- refuted here -/
  | refuted
  deriving DecidableEq, Repr

/-- Only kernel-proved content counts as closed. -/
def EvidenceV2.isClosed : EvidenceV2 → Bool
  | .kernelProved => true
  | _ => false

/-- The nodes of the Anchored V2 route. -/
inductive V2Node
  /-- the exact feedback-edge reduction and the `2 ^ β` branch bound -/
  | feedbackEdge
  /-- the `β = 2` four-test corollary -/
  | betaTwo
  /-- the certified block-cut / cactus exact decision -/
  | cactus
  /-- the affine path normal form and the integral root progression -/
  | affineNormalForm
  /-- the theta / bicyclic logical firewall -/
  | thetaFirewall
  /-- the tracked-prime kernel and its monotonicity -/
  | trackedKernel
  /-- the unit-list subset-sum theorem -/
  | unitSubsetSum
  /-- the coupled `2^e × p` charge theorem -/
  | coupledCharge
  /-- the finite coupled-batch extension theorem under an explicit supply record -/
  | finiteExtension
  /-- the weighted capacity function and its monotonicity -/
  | capacity
  /-- the negative capacity rejection certificate -/
  | negativeCapacity
  /-- the capacity incompleteness firewall -/
  | capacityGap
  /-- Level-2 fractional soundness -/
  | level2
  /-- forest Level-2 exactness (stretch goal, not attempted here) -/
  | forestLevel2
  /-- existence of a uniform negative capacity certificate on arising kernels -/
  | uniformNegativeCapacity
  /-- uniform Level-2 rejection on arising kernels -/
  | uniformLevel2Rejection
  /-- the external fixed-power coupled supply proposition -/
  | fixedPowerSupply
  /-- unrestricted Erdős #287 -/
  | erdos287
  deriving DecidableEq, Repr

/-- Evidence class of each Anchored V2 node. -/
def v2Evidence : V2Node → EvidenceV2
  | .feedbackEdge => .kernelProved
  | .betaTwo => .kernelProved
  | .cactus => .kernelProved
  | .affineNormalForm => .kernelProved
  | .thetaFirewall => .kernelProved
  | .trackedKernel => .kernelProved
  | .unitSubsetSum => .kernelProved
  | .coupledCharge => .kernelProved
  | .finiteExtension => .kernelProved
  | .capacity => .kernelProved
  | .negativeCapacity => .kernelProved
  | .capacityGap => .kernelProved
  | .level2 => .kernelProved
  | .forestLevel2 => .openNode
  | .uniformNegativeCapacity => .openNode
  | .uniformLevel2Rejection => .openNode
  | .fixedPowerSupply => .openNode
  | .erdos287 => .openNode

/-- The Anchored V2 cut: the new explicit certificate owners, the external supply proposition,
the stretch goal, and #287 itself. -/
def v2CutSet : List V2Node :=
  [.uniformNegativeCapacity, .uniformLevel2Rejection, .fixedPowerSupply, .forestLevel2,
    .erdos287]

/-- **`v2Cut_all_open`.**  `KERNEL-PROVED` bookkeeping. -/
theorem v2Cut_all_open : ∀ n ∈ v2CutSet, v2Evidence n = EvidenceV2.openNode := by
  intro n hn
  fin_cases hn <;> rfl

/-- **`v2_erdos287_open`.**  `KERNEL-PROVED` bookkeeping.  Erdős #287 is `OPEN` here. -/
theorem v2_erdos287_open : v2Evidence .erdos287 = EvidenceV2.openNode := rfl

/-! ## What the closed Anchored V2 nodes actually are -/

/-- **`feedbackEdge_closed`.**  `KERNEL-PROVED`.  The exact feedback-edge reduction with the
`2 ^ β` branch count. -/
theorem feedbackEdge_closed :
    v2Evidence .feedbackEdge = EvidenceV2.kernelProved ∧
      (∀ (I : ContactCSP) (F : Finset (ℕ × ℕ)), I.WellFormed → F ⊆ I.Edges →
        IsORContact I F →
          ((I.Sat ↔ ∃ S ∈ F.powerset, (branch I F S).Sat) ∧
            F.powerset.card = 2 ^ F.card)) :=
  ⟨rfl, fun I F hwf hF hOR => ⟨sat_iff_exists_branch I F hwf hF hOR, branch_count F⟩⟩

/-- **`cactus_closed`.**  `KERNEL-PROVED`.  The certified cactus decomposition decides
feasibility exactly, in both directions. -/
theorem cactus_closed :
    v2Evidence .cactus = EvidenceV2.kernelProved ∧
      (∀ (rel : ℕ → ℕ → Bool → Bool → Bool) (Cs : List ContactCSP) (a : ℕ),
        CactusData rel Cs a →
          ((unionCSP rel Cs).Sat ↔ ∃ x : Bool, ∀ J ∈ Cs, MsgAt J a x)) :=
  ⟨rfl, fun _ _ _ h => cactus_star_sat_iff h⟩

/-- **`thetaFirewall_closed`.**  `KERNEL-PROVED`.  A theta (`β = 2`) topology with balanced
affine transfers and locally feasible relations need not be contradictory. -/
theorem thetaFirewall_closed :
    v2Evidence .thetaFirewall = EvidenceV2.kernelProved ∧ ¬ ThetaBalancedRejection :=
  ⟨rfl, thetaBalancedRejection_false⟩

/-- **`negativeCapacity_closed`.**  `KERNEL-PROVED`.  A negative capacity certificate rejects
the actual anchored kernel. -/
theorem negativeCapacity_closed :
    v2Evidence .negativeCapacity = EvidenceV2.kernelProved ∧
      (∀ I : ContactCSP, I.WellFormed →
        (∀ e ∈ I.Edges, ∀ a b : Bool, I.rel e.1 e.2 a b = (a || b)) →
        NegativeCapacityCertificate (portOfContact I) → ¬ I.Sat) :=
  ⟨rfl, fun _ hwf hOR cert => negativeCapacity_rejects_anchored hwf hOR cert⟩

/-- **`capacityGap_closed`.**  `KERNEL-PROVED`.  Integral infeasibility does not imply a
negative Level-1 capacity certificate. -/
theorem capacityGap_closed :
    v2Evidence .capacityGap = EvidenceV2.kernelProved ∧
      (¬ gapSystem.Feasible ∧ (NegativeCapacityCertificate gapSystem → False)) :=
  ⟨rfl, capacity_incompleteness⟩

/-- **`level2_closed`.**  `KERNEL-PROVED`.  Level-2 fractional infeasibility rejects the actual
anchored kernel. -/
theorem level2_closed :
    v2Evidence .level2 = EvidenceV2.kernelProved ∧
      (∀ I : ContactCSP, I.WellFormed →
        (∀ e ∈ I.Edges, ∀ a b : Bool, I.rel e.1 e.2 a b = (a || b)) →
        ¬ (portOfContact I).Level2FractionalFeasible → ¬ I.Sat) :=
  ⟨rfl, fun _ hwf hOR h => level2_rejects_anchored hwf hOR h⟩

/-! ## Refinement of the Anchored V1 open owner -/

/-- **`v1_owner_refined`.**  `KERNEL-PROVED`.  The Anchored V1 global branching owner is
*refined*, not deleted: each of the two new certificate owners implies it (for kernels with
contact (OR) relations), and the unconditional form remains refuted. -/
theorem v1_owner_refined (Arises : ContactCSP → Prop)
    (hwf : ∀ I, Arises I → I.WellFormed)
    (hOR : ∀ I, Arises I → ∀ e ∈ I.Edges, ∀ a b : Bool, I.rel e.1 e.2 a b = (a || b)) :
    (UniformNegativeCapacity Arises → BranchingKernelRejection Arises) ∧
    (UniformLevel2Rejection Arises → BranchingKernelRejection Arises) ∧
    Anchored.anchoredEvidence .branchingKernelRejection = Anchored.EvidenceAnchored.openNode ∧
    ¬ BranchingKernelRejection (fun _ => True) :=
  ⟨branchingKernelRejection_of_uniformNegativeCapacity hwf hOR,
    branchingKernelRejection_of_uniformLevel2Rejection hwf hOR,
    rfl, branchingKernelRejection_unconditional_false⟩

/-! ## Reconciliation with the existing routes -/

/-- **`v2_routes_preserved`.**  `KERNEL-PROVED`.  The Route-S, Route-D and Anchored-V1 ledgers
and cut sets are unchanged by this namespace, and all four cuts remain simultaneously open. -/
theorem v2_routes_preserved :
    Effectivity.latestEvidence .erdos287 = Effectivity.EvidenceLatest.openNode ∧
    (∀ n ∈ Direct.directCutSet, Direct.directEvidence n = Direct.EvidenceDirect.openNode) ∧
    (∀ n ∈ Anchored.anchoredCutSet,
      Anchored.anchoredEvidence n = Anchored.EvidenceAnchored.openNode) ∧
    (∀ n ∈ v2CutSet, v2Evidence n = EvidenceV2.openNode) :=
  ⟨rfl, Direct.directCut_all_open, Anchored.anchoredCut_all_open, v2Cut_all_open⟩

/-- **`v2_finite_frontier_unchanged`.**  `KERNEL-PROVED`.  The certified finite frontier is
exactly the existing ceiling `67108856338751594`, with `U2` still pending; Anchored V2 adds no
finite exclusion and does **not** extend the frontier. -/
theorem v2_finite_frontier_unchanged :
    (∀ {A : Finset ℕ} (h : Erdos287Counterexample A),
        A.max' h.nonempty ≤ extendedCeiling → False) ∧
      extendedCeiling = 67108856338751594 ∧
      extendedCeiling < Effectivity.U2 ∧
      Effectivity.latestEvidence .finiteCeilingU2 =
        Effectivity.EvidenceLatest.pendingExternalImport :=
  Anchored.anchored_finite_frontier_unchanged

/-- **`v2_open_frontier`.**  `KERNEL-PROVED`.  No open Anchored V2 node is tagged closed, and
none of the three new owners is inhabited here. -/
theorem v2_open_frontier :
    (∀ n ∈ v2CutSet, (v2Evidence n).isClosed = false) ∧
      v2Evidence .uniformNegativeCapacity = EvidenceV2.openNode ∧
      v2Evidence .uniformLevel2Rejection = EvidenceV2.openNode ∧
      v2Evidence .fixedPowerSupply = EvidenceV2.openNode ∧
      v2Evidence .erdos287 = EvidenceV2.openNode := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  intro n hn
  fin_cases hn <;> rfl

end AnchoredV2
end Erdos287
