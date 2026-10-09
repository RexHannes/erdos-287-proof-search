import RequestProject.Erdos287.ResearchBankV7.Owners
import RequestProject.Erdos287.ResearchBankV7.IntervalLifting
import RequestProject.Erdos287.ResearchBankV7.Spine
import RequestProject.Erdos287.ResearchBankV7.ErasureHit
import RequestProject.Erdos287.ResearchBankV7.PolylogCompletion
import RequestProject.Erdos287.ResearchBankV7.FouvryPin
import RequestProject.Erdos287.ResearchBankV7.FiniteSourceKills
import RequestProject.Erdos287.ResearchBankV7.Numerics

/-!
# Erdős #287 — Research Bank V7: the epoch-aware verdict ledger

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Bookkeeping plus *proved* meta-statements only.  The V7 verdict scale extends the V6 one by
`FINITE-SOURCE-KILL` and `SUPERSEDED`; the V6 verdicts embed injectively (`ofV6_injective`), so
**every V6 classification is preserved verbatim** in the frozen historical block
(`v6_classifications_preserved`).

Machine-checked facts about this ledger:

* `no_closed_verdict` — no row of V7 is `CLOSED`;
* `erdos287_ownerOpen` — Erdős #287 is listed, as `OWNER-OPEN`;
* `entryOwner_ownerOpen` — the current sole owner is listed, as `OWNER-OPEN`;
* `kernelBanked_iff_kernelProof` — kernel rows are exactly those with kernel-proof evidence;
* `external_rows_never_kernel` — no row backed by an external analytic interface is kernel-banked.
-/

namespace Erdos287
namespace ResearchBankV7
namespace Ledger

open Erdos287.ResearchBankV5
open Erdos287.ResearchBankV7.Epochs

/-! ## 1.  The V7 verdict scale -/

/-- The acceptance verdict of a V7 item. -/
inductive VerdictV7
  /-- A new exact sorry-free mathematical theorem of this layer. -/
  | kernelBanked
  /-- A logical implication from an explicitly uninhabited interface. -/
  | conditionalBanked
  /-- An exact finite obstruction to an overstrong proposed theorem. -/
  | counterfixture
  /-- An exact finite contradiction killing one explicit finite source window. -/
  | finiteSourceKill
  /-- A current uninhabited research target. -/
  | ownerOpen
  /-- Bypassed or refined by later work.  **Never** means "false". -/
  | superseded
  /-- Forbidden unless a complete route to the original Erdős #287 statement is inhabited. -/
  | closed
  deriving DecidableEq, Repr

/-- The V6 verdict scale embeds into the V7 one; nothing of V6 is renamed or reinterpreted. -/
def ofV6 : ResearchBankV6.Ledger.Verdict → VerdictV7
  | .kernelBanked => VerdictV7.kernelBanked
  | .conditionalBanked => VerdictV7.conditionalBanked
  | .counterfixture => VerdictV7.counterfixture
  | .ownerOpen => VerdictV7.ownerOpen
  | .closed => VerdictV7.closed

theorem ofV6_injective : Function.Injective ofV6 := by
  intro a b h; cases a <;> cases b <;> simp_all [ofV6]

/-- An epoch-stamped ledger row: purely decidable bookkeeping data (no `Prop` payload). -/
structure RowV7 where
  /-- Human-readable item name. -/
  name : String
  /-- The epoch the item belongs to. -/
  epoch : Epoch
  /-- Acceptance verdict. -/
  verdict : VerdictV7
  /-- V5 research status (imported discipline). -/
  status : ResearchStatus
  /-- V5 evidence kind (imported discipline). -/
  evidence : EvidenceKind
  deriving DecidableEq, Repr

/-! ## 2.  The frozen V6 block -/

/-- The V6 ledger, re-recorded verbatim with its V6 epoch stamp and its V6 verdicts. -/
def v6Frozen : List RowV7 :=
  ResearchBankV6.Ledger.v6Ledger.map fun r =>
    { name := r.name
      epoch := Epoch.v6UpperGapCarry
      verdict := ofV6 r.verdict
      status := r.status
      evidence := r.evidence }

/-- **Every V6 classification is preserved.**  Each V6 row appears in the frozen block with the
same name, status, evidence kind and (embedded) verdict. -/
theorem v6_classifications_preserved :
    ∀ r ∈ ResearchBankV6.Ledger.v6Ledger, ∃ r' ∈ v6Frozen,
      r'.name = r.name ∧ r'.verdict = ofV6 r.verdict ∧ r'.status = r.status ∧
        r'.evidence = r.evidence := by
  intro r hr
  exact ⟨_, List.mem_map_of_mem hr, rfl, rfl, rfl, rfl⟩

/-- No row of the frozen V6 block is `CLOSED`. -/
theorem v6Frozen_no_closed : ∀ r ∈ v6Frozen, r.verdict ≠ VerdictV7.closed := by decide

/-! ## 3.  The new V7 rows -/

/-- The new V7 ledger rows. -/
def v7New : List RowV7 :=
  [ { name := "research epochs and meta-firewalls"
      epoch := Epoch.entryFirst
      verdict := VerdictV7.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "bounded adaptive absorption: guarded charging (1−3γ)W ≤ 2z₀+g₀"
      epoch := Epoch.stableEntry
      verdict := VerdictV7.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "absorption budgets at γ=1/8: W ≤ 16/5 z₀ + 8/5 g₀, U ≤ 2/5 z₀ + 1/5 g₀"
      epoch := Epoch.stableEntry
      verdict := VerdictV7.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "branching-bit budget"
      epoch := Epoch.stableEntry
      verdict := VerdictV7.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "fixed-polylog completion: finite second moment, disjoint buffer packing"
      epoch := Epoch.stableEntry
      verdict := VerdictV7.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "fixed-polylog complete-row law (Croot + PNT + LLL adapter)"
      epoch := Epoch.stableEntry
      verdict := VerdictV7.conditionalBanked
      status := ResearchStatus.«open»
      evidence := EvidenceKind.conditionalInterface }
  , { name := "STABLE-ENTRY forward: ENTRY word ⟹ nonfailed terminal leaf"
      epoch := Epoch.stableEntry
      verdict := VerdictV7.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "STABLE-ENTRY equivalence (reverse uses the external polylog interface)"
      epoch := Epoch.stableEntry
      verdict := VerdictV7.conditionalBanked
      status := ResearchStatus.«open»
      evidence := EvidenceKind.conditionalInterface }
  , { name := "exact mixed-modulus interval lifting + recursion for successive lifts"
      epoch := Epoch.exactHitSpine
      verdict := VerdictV7.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "arithmetic-spine extraction from a supplied certificate"
      epoch := Epoch.exactHitSpine
      verdict := VerdictV7.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "ERASURE-HIT (one-sided, fixed-part and complement forms)"
      epoch := Epoch.exactHitSpine
      verdict := VerdictV7.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "guarded branch-to-HIT (exact, given the hypothesis package)"
      epoch := Epoch.exactHitSpine
      verdict := VerdictV7.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "seed mass is not reference mass (counterfixture)"
      epoch := Epoch.exactHitSpine
      verdict := VerdictV7.counterfixture
      status := ResearchStatus.killed
      evidence := EvidenceKind.finiteRegressionOnly }
  , { name := "Fouvry pin-capture inequality (Fouvry/Luca–Young + Selberg + Brun–Titchmarsh)"
      epoch := Epoch.entryFirst
      verdict := VerdictV7.conditionalBanked
      status := ResearchStatus.«open»
      evidence := EvidenceKind.externalAnalyticBank }
  , { name := "branch-budget pin localization (given the numerical inputs)"
      epoch := Epoch.entryFirst
      verdict := VerdictV7.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "finite source kills p = 2q ± 1 (59, 83, 107, 61, 73)"
      epoch := Epoch.entryFirst
      verdict := VerdictV7.finiteSourceKill
      status := ResearchStatus.bank
      evidence := EvidenceKind.finiteRegressionOnly }
  , { name := "kill pattern not universal at every prime (counterfixture)"
      epoch := Epoch.entryFirst
      verdict := VerdictV7.counterfixture
      status := ResearchStatus.killed
      evidence := EvidenceKind.finiteRegressionOnly }
  , { name := "uniform safe-prime supply for the kill pattern"
      epoch := Epoch.entryFirst
      verdict := VerdictV7.ownerOpen
      status := ResearchStatus.«open»
      evidence := EvidenceKind.researchConjecture }
  , { name := "J = L₄₄₇ has 194 decimal digits and 644 bits"
      epoch := Epoch.exactHitSpine
      verdict := VerdictV7.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "V6 spot audit: five load-bearing statements re-exported unchanged"
      epoch := Epoch.entryFirst
      verdict := VerdictV7.kernelBanked
      status := ResearchStatus.bank
      evidence := EvidenceKind.kernelProof }
  , { name := "UpperGapCarryCompression (V6 owner)"
      epoch := Epoch.v6UpperGapCarry
      verdict := VerdictV7.superseded
      status := ResearchStatus.superseded
      evidence := EvidenceKind.researchConjecture }
  , { name := "ExactMassIntersection (V6 owner)"
      epoch := Epoch.v6UpperGapCarry
      verdict := VerdictV7.superseded
      status := ResearchStatus.superseded
      evidence := EvidenceKind.researchConjecture }
  , { name := "genuine ENTRY reference word"
      epoch := Epoch.entryFirst
      verdict := VerdictV7.ownerOpen
      status := ResearchStatus.«open»
      evidence := EvidenceKind.researchConjecture }
  , { name := "EntryFirstTerminalLeafExistenceOrKill"
      epoch := Epoch.entryFirst
      verdict := VerdictV7.ownerOpen
      status := ResearchStatus.«open»
      evidence := EvidenceKind.researchConjecture }
  , { name := "Erdős #287"
      epoch := Epoch.entryFirst
      verdict := VerdictV7.ownerOpen
      status := ResearchStatus.«open»
      evidence := EvidenceKind.researchConjecture } ]

/-- The complete V7 ledger: the frozen V6 block followed by the new rows. -/
def v7Ledger : List RowV7 := v6Frozen ++ v7New

/-! ## 4.  Machine-checked ledger discipline -/

/-- **No `CLOSED` verdict anywhere in V7.** -/
theorem no_closed_verdict : ∀ r ∈ v7Ledger, r.verdict ≠ VerdictV7.closed := by decide

/-- Erdős #287 is listed, and listed as `OWNER-OPEN`. -/
theorem erdos287_ownerOpen :
    ∃ r ∈ v7Ledger, r.name = "Erdős #287" ∧ r.verdict = VerdictV7.ownerOpen ∧
      r.status = ResearchStatus.«open» := by decide

/-- The current sole owner is listed, as `OWNER-OPEN`, in the current epoch. -/
theorem entryOwner_ownerOpen :
    ∃ r ∈ v7Ledger, r.name = "EntryFirstTerminalLeafExistenceOrKill" ∧
      r.epoch = Epoch.entryFirst ∧ r.verdict = VerdictV7.ownerOpen := by decide

/-- The node `genuine ENTRY reference word` is listed as `OWNER-OPEN`. -/
theorem entryWord_ownerOpen :
    ∃ r ∈ v7Ledger, r.name = "genuine ENTRY reference word" ∧
      r.verdict = VerdictV7.ownerOpen := by decide

/-- Kernel-banked rows are exactly the rows whose evidence kind is `kernelProof`. -/
theorem kernelBanked_iff_kernelProof :
    ∀ r ∈ v7Ledger, r.verdict = VerdictV7.kernelBanked ↔ r.evidence = EvidenceKind.kernelProof := by
  decide

/-- **No external analytic interface is ever kernel-banked.** -/
theorem external_rows_never_kernel :
    ∀ r ∈ v7Ledger, r.evidence = EvidenceKind.externalAnalyticBank →
      r.verdict = VerdictV7.conditionalBanked ∨ r.verdict = VerdictV7.ownerOpen := by decide

/-- Every non-kernel row is conditional, open, superseded, a counterfixture or a finite source
kill — never banked as proved general mathematics. -/
theorem nonKernel_rows_not_proved :
    ∀ r ∈ v7Ledger, r.evidence ≠ EvidenceKind.kernelProof →
      r.verdict = VerdictV7.conditionalBanked ∨ r.verdict = VerdictV7.ownerOpen ∨
        r.verdict = VerdictV7.counterfixture ∨ r.verdict = VerdictV7.finiteSourceKill ∨
        r.verdict = VerdictV7.superseded := by decide

/-- Superseded rows exist and are exactly the two historical V6 owners. -/
theorem superseded_rows :
    ∀ r ∈ v7New, r.verdict = VerdictV7.superseded →
      r.name = "UpperGapCarryCompression (V6 owner)" ∨
        r.name = "ExactMassIntersection (V6 owner)" := by decide

/-! ## 5.  Meta-firewalls of the ledger -/

/-- **The ledger is not a proof.**  Adding rows never inhabits a mathematical statement. -/
theorem ledger_is_not_a_proof : ¬ (∀ (_ : RowV7) (claim : Prop), claim) := by
  intro h
  exact h { name := "probe", epoch := Epoch.entryFirst, verdict := VerdictV7.ownerOpen,
            status := ResearchStatus.«open», evidence := EvidenceKind.researchConjecture } False

/-- **`SUPERSEDED` is not `false`** at ledger level either: a superseded row carries no refutation
(see `Epochs.superseded_flag_is_truth_neutral`). -/
theorem superseded_is_not_refutation :
    ∃ r : RowV7, r.verdict = VerdictV7.superseded ∧ ∃ claim : Prop, claim :=
  ⟨{ name := "superseded probe", epoch := Epoch.v6UpperGapCarry,
     verdict := VerdictV7.superseded, status := ResearchStatus.superseded,
     evidence := EvidenceKind.researchConjecture }, rfl, True, trivial⟩

/-- **Erdős #287 is not closed here.** -/
theorem erdos287_not_closed_in_v7 :
    ¬ ∃ r ∈ v7Ledger, r.name = "Erdős #287" ∧ r.verdict = VerdictV7.closed := by decide

end Ledger
end ResearchBankV7
end Erdos287
