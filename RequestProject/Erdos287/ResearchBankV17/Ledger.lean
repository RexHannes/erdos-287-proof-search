import RequestProject.Erdos287.ResearchBankV16.Ledger
import RequestProject.Erdos287.ResearchBankV17.ThinEffectivityFirewall

/-!
# Erdős #287 — Research Bank V17: ledger (append-only)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`v17Ledger = v16Ledger ++ v17New` (V16 ledger preserved as a prefix).
-/

namespace Erdos287
namespace ResearchBankV17
namespace Ledger

open ResearchBankV16.Ledger

def v17New : List RowV16 :=
  [ .new "thin parameters (delta = 1/40000, L = 41252000, a = 28593810)" .finiteRegression
  , .new "corrected log P = (L+2) log 2 + log 3" .leanBank
  , .new "old verifier formula L log 2 + log 3 (= log 3K)" .repairedRetired
  , .new "thin functional certificate (corrected strict bounds)" .externalProvider
  , .new "functional certificate vs arithmetic moments separated" .leanBank
  , .new "uniform thinning arithmetic (L_delta, b, a = b + 120)" .leanBank
  , .new "FunctionalThinningProvider" .externalProvider
  , .new "uniform functional thinning (delta -> tuple -> x)" .leanConditional
  , .new "uniformity in x and delta simultaneously" .repairedRetired
  , .new "thin support exponent comparisons 4/7 < 7/12 < 3/5" .leanBank
  , .new "support level below threshold constructs prime provider" .repairedRetired
  , .new "Route-C-thin consumer" .leanConditional
  , .new "explicit analytic threshold" .open
  , .new "finite splice" .open
  , .new "Erdős #287" .open ]

def v17Ledger : List RowV16 := v16Ledger ++ v17New

theorem v17_preserves_v16_ledger :
    v17Ledger.take v16Ledger.length = v16Ledger ∧ ∀ r ∈ v16Ledger, r ∈ v17Ledger :=
  ⟨List.take_left, fun _ hr => List.mem_append_left _ hr⟩

theorem v17_erdos287_open : ∀ r ∈ v17New, r.nm = "Erdős #287" → r.cls? = some .open := by
  decide

end Ledger
end ResearchBankV17
end Erdos287
