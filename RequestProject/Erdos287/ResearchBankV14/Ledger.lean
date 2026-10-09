import RequestProject.Erdos287.ResearchBankV14.EffectivityFirewall

/-!
# Erdős #287 — Research Bank V14: ledger (append-only)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `RowV14` — either a verbatim V13 row (`RowV14.old`, so no V12/V13 row is re-interpreted) or a
  new V14 row;
* `v14Ledger = (v13Ledger.map RowV14.old) ++ v14New`;
* `v14_preserves_v13_ledger` — the embedded V13 ledger is a prefix and the embedding is
  injective;
* `v14_status_ledger` — the V14 statuses; `v14_erdos287_open` — #287 stays OPEN;
  `v14_no_open_item_promoted` — the useful-height bound, the explicit analytic threshold and the
  finite splice remain OPEN.
-/

namespace Erdos287
namespace ResearchBankV14
namespace Ledger

open ResearchBankV8.Ledger ResearchBankV12.Ledger

/-- V14/V15 statuses. -/
inductive StatusV14
  /-- Banked in an earlier frozen layer. -/
  | bank
  /-- Kernel-proved in the Lean bank. -/
  | leanBank
  /-- Kernel-proved application of a general Lean theorem. -/
  | leanBankTheoremApplication
  /-- Lean implication conditional on named standard analytic providers. -/
  | leanBankConditionalOnStandardProviders
  /-- An open analytic provider (defined, never constructed). -/
  | openAnalyticProvider
  /-- Open. -/
  | open
  deriving DecidableEq, Repr

/-- A V14/V15 ledger row: a verbatim earlier row, or a new row. -/
inductive RowV14
  | old (r : RowV12)
  | new (name : String) (status : StatusV14) (evidence : EvidenceV8)
  deriving DecidableEq, Repr

/-- Row name. -/
def RowV14.nm : RowV14 → String
  | .old r => r.name
  | .new n _ _ => n

/-- New-row status (`none` for verbatim earlier rows). -/
def RowV14.st : RowV14 → Option StatusV14
  | .old _ => none
  | .new _ s _ => some s

theorem old_injective : Function.Injective RowV14.old := fun _ _ h => by cases h; rfl

/-- The new V14 rows. -/
def v14New : List RowV14 :=
  [ .new "ResearchBankV12" .bank .researchRecord
  , .new "ResearchBankV13" .bank .researchRecord
  , .new "balanced functional score" .bank .externalInterface
  , .new "G(11,2): alpha = 3, proper 4-colouring" .leanBank .kernelProof
  , .new "symbolic balanced blow-up" .leanBank .kernelProof
  , .new "edge-only compiler theorem (prescribed boxes, general finite graph)" .leanBank
      .kernelProof
  , .new "11-cell compiler existence" .leanBankTheoremApplication .kernelProof
  , .new "compiler useful-height bound" .open .researchRecord
  , .new "contact annulus" .leanBank .kernelProof
  , .new "useful consecutive identity (orientation fixed)" .leanBank .kernelProof
  , .new "score combinatorics" .leanBank .kernelProof
  , .new "row rigidity" .leanBank .kernelProof
  , .new "harmonic two-hole contradiction (c = 37/100)" .leanBank .kernelProof
  , .new "conditional source-to-#287 implication" .leanBank .conditionalOnInterfaces
  , .new "explicit analytic threshold" .open .researchRecord
  , .new "finite splice" .open .researchRecord
  , .new "Erdős #287" .open .researchRecord ]

/-- The complete V14 ledger. -/
def v14Ledger : List RowV14 := (ResearchBankV13.Ledger.v13Ledger.map RowV14.old) ++ v14New

/-- **V14 preserves the V13 ledger** verbatim (prefix, injective embedding). -/
theorem v14_preserves_v13_ledger :
    v14Ledger.take ResearchBankV13.Ledger.v13Ledger.length =
      ResearchBankV13.Ledger.v13Ledger.map RowV14.old ∧
    ∀ r ∈ ResearchBankV13.Ledger.v13Ledger, RowV14.old r ∈ v14Ledger := by
  refine ⟨?_, fun r hr => List.mem_append_left _ (List.mem_map_of_mem hr)⟩
  unfold v14Ledger
  rw [← List.length_map (f := RowV14.old)]
  exact List.take_left

/-- **The V14 status ledger.** -/
theorem v14_status_ledger :
    .new "11-cell compiler existence" .leanBankTheoremApplication .kernelProof ∈ v14New ∧
    .new "compiler useful-height bound" .open .researchRecord ∈ v14New ∧
    .new "contact annulus" .leanBank .kernelProof ∈ v14New ∧
    .new "useful consecutive identity (orientation fixed)" .leanBank .kernelProof ∈ v14New ∧
    .new "row rigidity" .leanBank .kernelProof ∈ v14New ∧
    .new "conditional source-to-#287 implication" .leanBank .conditionalOnInterfaces ∈ v14New ∧
    .new "explicit analytic threshold" .open .researchRecord ∈ v14New ∧
    .new "finite splice" .open .researchRecord ∈ v14New := by
  decide

/-- **Erdős #287 stays OPEN**: every new row named "Erdős #287" has status OPEN. -/
theorem v14_erdos287_open : ∀ r ∈ v14New, r.nm = "Erdős #287" → r.st = some .open := by decide

/-- The open items are not promoted. -/
theorem v14_no_open_item_promoted :
    ∀ r ∈ v14New, r.nm ∈ ["compiler useful-height bound", "explicit analytic threshold",
      "finite splice", "Erdős #287"] → r.st = some .open := by decide

end Ledger
end ResearchBankV14
end Erdos287
