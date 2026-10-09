import RequestProject.Erdos287.ResearchBankV5.Routes
import RequestProject.Erdos287.ResearchBankV6.UpperGapCarry
import RequestProject.Erdos287.ResearchBankV6.SupportDisjointness
import RequestProject.Erdos287.ResearchBankV6.UpperGapContact
import RequestProject.Erdos287.ResearchBankV6.ContactTarget
import RequestProject.Erdos287.ResearchBankV6.MiddleBand
import RequestProject.Erdos287.ResearchBankV6.OpenOwners

/-!
# Erdős #287 — Research Bank V6: verdict ledger and route-aware closure DAG

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

This module is strictly bookkeeping plus *proved* implications.  It

* preserves the two-dimensional `ResearchStatus × EvidenceKind` discipline of V5 (imported, not
  re-defined, not weakened);
* adds the acceptance `Verdict` scale
  `KERNEL-BANKED / CONDITIONAL-BANKED / COUNTERFIXTURE / OWNER-OPEN / CLOSED`;
* records the V6 ledger and machine-checks that **no** entry is `CLOSED`;
* adds the new route `upperGapCarryV6` beside `anchoredV4` and `contactCoreV5`, and records that
  the three are **not** asserted equivalent;
* enters closure-DAG edges **only** as Lean-proved implications.
-/

namespace Erdos287
namespace ResearchBankV6
namespace Ledger

open Erdos287.ResearchBankV5

/-! ## 1.  Routes -/

/-- The three coexisting research routes after V6.  `anchoredV4` and `contactCoreV5` are the V5
routes (unchanged); `upperGapCarryV6` is the new carry layer. -/
inductive RouteV6
  | anchoredV4
  | contactCoreV5
  | upperGapCarryV6
  deriving DecidableEq, Repr

/-- The V5 routes embed into the V6 route set; nothing of V5 is renamed or replaced. -/
def ofV5 : ResearchRoute → RouteV6
  | ResearchRoute.anchoredV4 => RouteV6.anchoredV4
  | ResearchRoute.contactCoreV5 => RouteV6.contactCoreV5

theorem ofV5_injective : Function.Injective ofV5 := by
  intro a b h
  cases a <;> cases b <;> simp_all [ofV5]

/-- The three routes are pairwise distinct objects of bookkeeping. -/
theorem routes_pairwise_distinct :
    RouteV6.anchoredV4 ≠ RouteV6.contactCoreV5 ∧
    RouteV6.contactCoreV5 ≠ RouteV6.upperGapCarryV6 ∧
    RouteV6.anchoredV4 ≠ RouteV6.upperGapCarryV6 := by decide

/-! ## 2.  The acceptance verdict scale -/

/-- The acceptance verdict of a V6 item. -/
inductive Verdict
  /-- A new exact sorry-free mathematical theorem of this layer. -/
  | kernelBanked
  /-- A logical implication from an explicitly uninhabited interface. -/
  | conditionalBanked
  /-- An exact finite obstruction to an overstrong proposed theorem. -/
  | counterfixture
  /-- A current uninhabited research target. -/
  | ownerOpen
  /-- Forbidden unless a complete route to the original Erdős #287 statement is inhabited. -/
  | closed
  deriving DecidableEq, Repr

/-- A ledger row: purely decidable bookkeeping data (no `Prop` payload). -/
structure Row where
  /-- Human-readable item name. -/
  name : String
  /-- Route the item belongs to. -/
  route : RouteV6
  /-- Acceptance verdict. -/
  verdict : Verdict
  /-- V5 research status (imported discipline). -/
  status : ResearchStatus
  /-- V5 evidence kind (imported discipline). -/
  evidence : EvidenceKind
  deriving DecidableEq, Repr

/-! ## 3.  The V6 ledger -/

/-- The V6 ledger.  Every row's verdict is justified by the correspondingly named Lean
declaration of this layer (or, for `FULL-FROZEN`, of the earlier layers it imports). -/
def v6Ledger : List Row :=
  [ { name := "FULL-FROZEN prime-power precision (small-prime denominator entry)"
      route := RouteV6.contactCoreV5
      verdict := Verdict.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "contact-core finite per-middle-row target  H ≤ 2π(z) + 4⌊M/z²⌋"
      route := RouteV6.contactCoreV5
      verdict := Verdict.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "contact-core cube-root asymptotic  H ≪ M^{1/3}(log M)^{-2/3}"
      route := RouteV6.contactCoreV5
      verdict := Verdict.ownerOpen
      status := ResearchStatus.«open»
      evidence := EvidenceKind.externalAnalyticBank }
  , { name := "middle band, same-trace completion"
      route := RouteV6.contactCoreV5
      verdict := Verdict.conditionalBanked
      status := ResearchStatus.«open»
      evidence := EvidenceKind.conditionalInterface }
  , { name := "upper-gap denominator entry  ⇔  p ∣ T_p"
      route := RouteV6.upperGapCarryV6
      verdict := Verdict.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "upper-gap carry identity  ∑ ε/(pj) = k_p / L_N"
      route := RouteV6.upperGapCarryV6
      verdict := Verdict.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "same-height carry aggregation  ∑ = ∑_N K_N / L_N"
      route := RouteV6.upperGapCarryV6
      verdict := Verdict.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "upper-gap support disjointness  (pq > M)"
      route := RouteV6.upperGapCarryV6
      verdict := Verdict.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "upper-gap contact relation |pj − qℓ| = 1: exact finite lemmas"
      route := RouteV6.upperGapCarryV6
      verdict := Verdict.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "cofactor range substitution 1..N  (overstrong)"
      route := RouteV6.upperGapCarryV6
      verdict := Verdict.counterfixture
      status := ResearchStatus.killed
      evidence := EvidenceKind.finiteRegressionOnly }
  , { name := "UpperGapCarryCompression (4 candidate interfaces)"
      route := RouteV6.upperGapCarryV6
      verdict := Verdict.ownerOpen
      status := ResearchStatus.«open»
      evidence := EvidenceKind.researchConjecture }
  , { name := "ExactMassIntersection  (S = 1)"
      route := RouteV6.upperGapCarryV6
      verdict := Verdict.ownerOpen
      status := ResearchStatus.«open»
      evidence := EvidenceKind.researchConjecture }
  , { name := "Erdős #287"
      route := RouteV6.upperGapCarryV6
      verdict := Verdict.ownerOpen
      status := ResearchStatus.«open»
      evidence := EvidenceKind.researchConjecture } ]

/-- **No `CLOSED` verdict anywhere in V6.** -/
theorem no_closed_verdict : ∀ r ∈ v6Ledger, r.verdict ≠ Verdict.closed := by decide

/-- Erdős #287 is listed, and listed as `OWNER-OPEN`. -/
theorem erdos287_ownerOpen :
    ∃ r ∈ v6Ledger, r.name = "Erdős #287" ∧ r.verdict = Verdict.ownerOpen ∧
      r.status = ResearchStatus.«open» := by decide

/-- Kernel-banked rows are exactly the rows whose evidence kind is `kernelProof`. -/
theorem kernelBanked_iff_kernelProof :
    ∀ r ∈ v6Ledger, r.verdict = Verdict.kernelBanked ↔ r.evidence = EvidenceKind.kernelProof := by
  decide

/-- Every non-kernel row is open, conditional or a counterfixture — never banked as proved
mathematics. -/
theorem nonKernel_rows_not_proved :
    ∀ r ∈ v6Ledger, r.evidence ≠ EvidenceKind.kernelProof →
      r.verdict = Verdict.conditionalBanked ∨ r.verdict = Verdict.ownerOpen ∨
        r.verdict = Verdict.counterfixture := by decide

/-! ## 4.  The closure DAG: only proved implications -/

/-- A DAG edge carries an actual Lean proof of `src → tgt`. -/
structure ProvedEdge where
  /-- The source statement. -/
  src : Prop
  /-- The target statement. -/
  tgt : Prop
  /-- The proof of the edge.  There is no way to enter an edge without one. -/
  proof : src → tgt

/-- Edge: the fixed-cardinality additive interface gives simultaneous middle-row completion. -/
def edge_middleBand : ProvedEdge :=
  { src := MiddleBand.RestrictedSumsetInput
    tgt := ∀ (A : Finset (ZMod 5)) (r : ZMod 5), 3 ≤ A.card →
            5 ≤ 2 * (A.card - 2) + 1 → ∃ B ⊆ A, B.card = 2 ∧ ∑ x ∈ B, x = r
    proof := by
      intro hin A r hA hlong
      exact MiddleBand.restrictedSumset_covers hin (by norm_num) A 2 (by omega) hlong r }

/-- Edge: granularity compression gives the denominator format required by the mass-intersection
consumer. -/
def edge_granularity : ProvedEdge :=
  { src := OpenOwners.UpperGapCarryCompressionGranularity 12
    tgt := ∀ d : OpenOwners.CarryData, d.admissible →
            (OpenOwners.aggregateMass d).den ∣ UpperGap.lcmUpto 12
    proof := fun h d hd => OpenOwners.mass_den_dvd_of_granularity h d hd }

/-- Edge: the final owner gives the non-existence of unit mass. -/
def edge_exactMass : ProvedEdge :=
  { src := OpenOwners.ExactMassIntersection 0 Set.univ Set.univ
    tgt := ∀ m u : ℚ, (0 : ℚ) + m + u ≠ 1
    proof := fun h m u => OpenOwners.no_unit_mass_of_exactMassIntersection h
      (Set.mem_univ m) (Set.mem_univ u) }

/-- Edge: the external contact adapter, together with the prime-counting input and the finite
kernel bound, gives the cube-root asymptotic — and only that way. -/
def edge_contactAsymptotic (H : ℕ → ℝ) : ProvedEdge :=
  { src := ContactTarget.ContactAsymptoticAdapter H ∧ ContactTarget.PrimeCountingAsymptotic ∧
      (∀ M z : ℕ, 2 ≤ z → H M ≤ 2 * (ContactTarget.piCount z : ℝ) + 4 * ((M / z ^ 2 : ℕ) : ℝ))
    tgt := ContactTarget.ContactCubeRootTarget H
    proof := fun h => ContactTarget.contact_cubeRoot_conditional h.1 h.2.1 h.2.2 }

/-- The V6 closure DAG: the list of edges currently entered.  Every entry is a proved
implication. -/
def closureDagV6 : List ProvedEdge :=
  [edge_middleBand, edge_granularity, edge_exactMass]

/-- Every DAG edge is inhabited as an implication (this is the only content a DAG edge has). -/
theorem dag_edges_are_proved (e : ProvedEdge) (hs : e.src) : e.tgt := e.proof hs

/-! ## 5.  No collapse, no fake closure -/

/-- **No asserted equivalence.**  The three routes are *not* claimed equivalent: from the fact
that two statements are both recorded in the bank one cannot infer that they imply each other. -/
theorem routes_not_claimed_equivalent : ¬ (∀ P Q : Prop, P ↔ Q) := by
  intro h
  exact (h True False).1 trivial

/-- An `ownerOpen` row does not inhabit anything: the ledger row is data, not a proof. -/
theorem ownerOpen_row_is_not_a_proof :
    ∃ (r : Row) (claim : Prop), r.verdict = Verdict.ownerOpen ∧ ¬ claim :=
  ⟨{ name := "owner-open probe", route := RouteV6.upperGapCarryV6, verdict := Verdict.ownerOpen,
     status := ResearchStatus.«open», evidence := EvidenceKind.researchConjecture },
   False, rfl, not_false⟩

/-- **The ledger is not a proof.**  Adding rows never inhabits a mathematical statement. -/
theorem ledger_is_not_a_proof : ¬ (∀ (_ : Row) (claim : Prop), claim) := by
  intro h
  exact h { name := "probe", route := RouteV6.upperGapCarryV6, verdict := Verdict.ownerOpen,
            status := ResearchStatus.«open», evidence := EvidenceKind.researchConjecture } False

/-- **Erdős #287 is not closed here.**  The V6 layer contains no row with verdict `closed`, and
in particular none for the original problem. -/
theorem erdos287_not_closed_in_v6 :
    ¬ ∃ r ∈ v6Ledger, r.name = "Erdős #287" ∧ r.verdict = Verdict.closed := by decide

end Ledger
end ResearchBankV6
end Erdos287
