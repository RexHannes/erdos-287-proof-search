import RequestProject.Erdos287.ResearchBankV14.Ledger
import RequestProject.Erdos287.ResearchBankV15.ScopeFirewalls

/-!
# Erdős #287 — Research Bank V15: final ledger (append-only)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`v15Ledger = v14Ledger ++ v15New`; the V14 ledger (which itself embeds the V13 ledger verbatim)
is preserved as a prefix.  The final status summary (`v15_final_status`):

| item | status |
|---|---|
| ResearchBankV12, ResearchBankV13 | BANK |
| balanced functional score | BANK |
| 11-cell compiler existence | LEAN BANK / existing-theorem application |
| compiler useful-height bound | OPEN (not needed for asymptotic existence) |
| contact annulus | LEAN BANK |
| useful consecutive identity | LEAN BANK, orientation fixed |
| row rigidity | LEAN BANK |
| conditional source-to-#287 implication | LEAN BANK |
| fixed-source S0/S1 reduction | LEAN BANK conditional on named standard analytic providers |
| actual weighted coloured pair theorem | OPEN ANALYTIC PROVIDER |
| explicit analytic threshold | OPEN |
| finite splice | OPEN |
| Erdős #287 | OPEN |
-/

namespace Erdos287
namespace ResearchBankV15
namespace Ledger

open ResearchBankV8.Ledger ResearchBankV14.Ledger

/-- The new V15 rows. -/
def v15New : List RowV14 :=
  [ .new "fixed actual affine source" .leanBank .kernelProof
  , .new "derivative kernel G vs F" .openAnalyticProvider .externalInterface
  , .new "actual Moebius coefficients (shared primes allowed)" .leanBank .kernelProof
  , .new "complete lcm modulus / first-moment modulus a_i W0 q" .leanBank .kernelProof
  , .new "moving CRT residue" .leanBank .kernelProof
  , .new "collision local factors" .leanBank .kernelProof
  , .new "divisor multiplicity (finite grouping)" .leanBank .kernelProof
  , .new "normalization N_X = C_X S_W0(a) I" .leanBank .kernelProof
  , .new "ordinary Bombieri-Vinogradov provider" .openAnalyticProvider .externalInterface
  , .new "fixed-source S0/S1 reduction" .leanBankConditionalOnStandardProviders
      .conditionalOnInterfaces
  , .new "actual weighted coloured pair theorem" .openAnalyticProvider .externalInterface
  , .new "one-lemma conditional asymptotic reduction" .leanBankConditionalOnStandardProviders
      .conditionalOnInterfaces
  , .new "explicit analytic threshold" .open .researchRecord
  , .new "finite splice" .open .researchRecord
  , .new "Erdős #287" .open .researchRecord ]

/-- The complete V15 ledger. -/
def v15Ledger : List RowV14 := v14Ledger ++ v15New

/-- **V15 preserves the V14 ledger** (prefix). -/
theorem v15_preserves_v14_ledger :
    v15Ledger.take v14Ledger.length = v14Ledger ∧ ∀ r ∈ v14Ledger, r ∈ v15Ledger :=
  ⟨List.take_left, fun _ hr => List.mem_append_left _ hr⟩

/-- **The final status summary** (section D). -/
theorem v15_final_status :
    .new "ResearchBankV12" .bank .researchRecord ∈ v15Ledger ∧
    .new "ResearchBankV13" .bank .researchRecord ∈ v15Ledger ∧
    .new "balanced functional score" .bank .externalInterface ∈ v15Ledger ∧
    .new "11-cell compiler existence" .leanBankTheoremApplication .kernelProof ∈ v15Ledger ∧
    .new "compiler useful-height bound" .open .researchRecord ∈ v15Ledger ∧
    .new "contact annulus" .leanBank .kernelProof ∈ v15Ledger ∧
    .new "useful consecutive identity (orientation fixed)" .leanBank .kernelProof ∈ v15Ledger ∧
    .new "row rigidity" .leanBank .kernelProof ∈ v15Ledger ∧
    .new "conditional source-to-#287 implication" .leanBank .conditionalOnInterfaces ∈ v15Ledger ∧
    .new "fixed-source S0/S1 reduction" .leanBankConditionalOnStandardProviders
      .conditionalOnInterfaces ∈ v15Ledger ∧
    .new "actual weighted coloured pair theorem" .openAnalyticProvider .externalInterface ∈
      v15Ledger ∧
    .new "explicit analytic threshold" .open .researchRecord ∈ v15Ledger ∧
    .new "finite splice" .open .researchRecord ∈ v15Ledger ∧
    .new "Erdős #287" .open .researchRecord ∈ v15Ledger := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | exact List.mem_append_left _ (List.mem_append_right _ (by decide))
    | exact List.mem_append_right _ (by decide)

/-- **Erdős #287 stays OPEN** in every new V15 row. -/
theorem v15_erdos287_open : ∀ r ∈ v15New, r.nm = "Erdős #287" → r.st = some .open := by decide

/-- The pair theorem is an open analytic provider, never promoted. -/
theorem v15_pair_provider_open :
    ∀ r ∈ v15New, r.nm = "actual weighted coloured pair theorem" →
      r.st = some .openAnalyticProvider := by decide

/-- The open items are not promoted. -/
theorem v15_no_open_item_promoted :
    ∀ r ∈ v15New, r.nm ∈ ["explicit analytic threshold", "finite splice", "Erdős #287"] →
      r.st = some .open := by decide

end Ledger
end ResearchBankV15
end Erdos287
