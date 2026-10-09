import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V5: routes, evidence kinds and status firewalls

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This module is the meta-layer of the route-aware research bank.  It is strictly *bookkeeping*:
nothing here inhabits any open mathematical owner, and no ledger entry is ever used as a premise
of a mathematical theorem.

Two research routes coexist:

* `ResearchRoute.anchoredV4` — the frozen/banked Anchored V2 → V3 → V4 formal route;
* `ResearchRoute.contactCoreV5` — the newer CONTACT / strict-height / `p`-adic / exceptional-leaf
  route.

Neither supersedes the other.  They have different open-owner sets and different closure DAGs,
and the firewall theorems below record that a status statement about one route never transports
to the other.
-/

namespace Erdos287
namespace ResearchBankV5

/-! ## 1.  Routes -/

/-- The two currently distinct research routes towards Erdős #287. -/
inductive ResearchRoute
  | anchoredV4
  | contactCoreV5
  deriving DecidableEq, Repr

/-- The two routes are distinct objects of bookkeeping. -/
theorem route_distinct : ResearchRoute.anchoredV4 ≠ ResearchRoute.contactCoreV5 := by decide

/-! ## 2.  Evidence kinds and research statuses -/

/-- What *kind of evidence* supports a bank node. -/
inductive EvidenceKind
  /-- A Lean kernel proof in this project, with only standard axioms. -/
  | kernelProof
  /-- An externally banked analytic theorem, **not** formalized here. -/
  | externalAnalyticBank
  /-- A Lean implication whose premise is an uninhabited `Prop` parameter. -/
  | conditionalInterface
  /-- A finite regression/fixture check only; certifies no asymptotic statement. -/
  | finiteRegressionOnly
  /-- A research conjecture; no proof, internal or external. -/
  | researchConjecture
  deriving DecidableEq, Repr

/-- The research-programme status of a bank node. -/
inductive ResearchStatus
  /-- Recorded as available research state. -/
  | bank
  /-- Paid: the corresponding obligation has been discharged at its stated scope. -/
  | pay
  /-- Still open; nothing inhabits it. -/
  | «open»
  /-- No longer needed. -/
  | retired
  /-- The architecture is dead at its stated scope (never: the theorem is false). -/
  | killed
  /-- Replaced by a strictly stronger statement. -/
  | superseded
  /-- Closed at its stated scope. -/
  | closed
  deriving DecidableEq, Repr

/-- A bank node carries a route, a claim, a status **and** an evidence kind.  The only soundness
guarantee attached to a node is the one carried by `kernelProof`: if the evidence kind is
`kernelProof`, the claim is actually proved. -/
structure BankNode where
  /-- Which research route the node belongs to. -/
  route : ResearchRoute
  /-- Human-readable name. -/
  name : String
  /-- The mathematical claim of the node. -/
  claim : Prop
  /-- Research status. -/
  status : ResearchStatus
  /-- Evidence kind. -/
  evidence : EvidenceKind
  /-- The *only* soundness invariant: kernel-proved nodes are inhabited. -/
  kernel_sound : evidence = EvidenceKind.kernelProof → claim

/-! ## 3.  Status firewalls -/

/-- An externally banked analytic input is never a kernel proof. -/
theorem externalBank_not_kernelProof :
    EvidenceKind.externalAnalyticBank ≠ EvidenceKind.kernelProof := by decide

/-- A `conditionalInterface` node does **not** inhabit its claim: there is such a node whose claim
is `False`. -/
theorem conditionalInterface_not_inhabited :
    ∃ n : BankNode, n.evidence = EvidenceKind.conditionalInterface ∧ ¬ n.claim :=
  ⟨{ route := ResearchRoute.contactCoreV5
     name := "conditional-interface probe"
     claim := False
     status := ResearchStatus.bank
     evidence := EvidenceKind.conditionalInterface
     kernel_sound := by intro h; exact absurd h (by decide) }, rfl, id⟩

/-- The same for an `externalAnalyticBank` node: being recorded as banked research state never
inhabits the statement. -/
theorem externalBank_not_inhabited :
    ∃ n : BankNode, n.evidence = EvidenceKind.externalAnalyticBank ∧ ¬ n.claim :=
  ⟨{ route := ResearchRoute.contactCoreV5
     name := "external-bank probe"
     claim := False
     status := ResearchStatus.bank
     evidence := EvidenceKind.externalAnalyticBank
     kernel_sound := by intro h; exact absurd h (by decide) }, rfl, id⟩

/-- `open` is not `closed`. -/
theorem open_not_closed : ResearchStatus.«open» ≠ ResearchStatus.closed := by decide

/-- Killing a route is **not** falsifying a mathematical target: there is a `killed` node whose
claim is true. -/
theorem killed_not_false_target :
    ∃ n : BankNode, n.status = ResearchStatus.killed ∧ n.claim :=
  ⟨{ route := ResearchRoute.contactCoreV5
     name := "killed-architecture probe"
     claim := True
     status := ResearchStatus.killed
     evidence := EvidenceKind.kernelProof
     kernel_sound := fun _ => trivial }, rfl, trivial⟩

/-- Superseding a statement is not falsifying it. -/
theorem superseded_not_false :
    ∃ n : BankNode, n.status = ResearchStatus.superseded ∧ n.claim :=
  ⟨{ route := ResearchRoute.anchoredV4
     name := "superseded-owner probe"
     claim := True
     status := ResearchStatus.superseded
     evidence := EvidenceKind.kernelProof
     kernel_sound := fun _ => trivial }, rfl, trivial⟩

/-- Kernel-proved nodes really are inhabited (the one direction of the invariant that holds). -/
theorem kernelProof_inhabited (n : BankNode) (h : n.evidence = EvidenceKind.kernelProof) :
    n.claim := n.kernel_sound h

/-! ## 4.  Route firewall -/

/-- **Route firewall.**  Openness does not propagate between statements: from `¬ P` one cannot
deduce `¬ Q` for an unrelated `Q`.  In particular `AnchoredV4 ENTRY_EXISTENCE OPEN` does not make
`ContactCore Gate A OPEN`, nor conversely. -/
theorem open_status_does_not_propagate : ¬ (∀ P Q : Prop, ¬ P → ¬ Q) := by
  intro h
  exact (h False True not_false) trivial

/-- Concrete witness of route independence in the `anchoredV4 → contactCoreV5` direction: an
uninhabited V4 owner can coexist with an inhabited contact-core statement. -/
theorem anchored_open_contact_closed_possible :
    ∃ entry gateA : Prop, ¬ entry ∧ gateA := ⟨False, True, not_false, trivial⟩

/-- Concrete witness of route independence in the `contactCoreV5 → anchoredV4` direction. -/
theorem contact_open_anchored_closed_possible :
    ∃ gateA entry : Prop, ¬ gateA ∧ entry := ⟨False, True, not_false, trivial⟩

/-- **No closure without a bridge.**  A route-final configuration never yields the original
problem by bookkeeping alone; an explicit proved bridge theorem is required. -/
theorem no_closure_without_bridge : ¬ (∀ finalConfig original : Prop, finalConfig → original) := by
  intro h
  exact h True False trivial

/-- A route-level bridge is exactly the object that transports a closure, and it must be supplied
as a proof. -/
theorem closure_transports_only_along_bridge
    (finalConfig original : Prop) (bridge : finalConfig → original) (hfin : finalConfig) :
    original := bridge hfin

end ResearchBankV5
end Erdos287
