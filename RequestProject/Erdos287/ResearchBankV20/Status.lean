import RequestProject.Erdos287.ResearchBankV19.Ledger
import RequestProject.Erdos287.ResearchBankV20.ScopeFirewalls

/-!
# Erdős #287 — Research Bank V20: final status / ledger (append-only)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The V20 ledger is the V19 ledger (itself containing V15 verbatim and the V16–V19 rows) followed by
the V20 rows.  `v20_final_status` machine-checks the required top-level classification; in
particular `ActualCenteredSourceCompositionProvider`, explicit `M₀`, finite splice and global
Erdős #287 are `OPEN`, and the thin pair theorem and asymptotic #287 are `LEAN CONDITIONAL` only.
-/

namespace Erdos287
namespace ResearchBankV20
namespace Status

open ResearchBankV16.Ledger

def v20New : List RowV16 :=
  [ .new "V14/V15 infrastructure" .leanBank
  , .new "Route-C graph / score / contact infrastructure" .leanBank
  , .new "Route-C conditional implication" .leanConditional
  , .new "Route-C-thin corrected functional consumer (certified-input dependent)" .leanConditional
  , .new "reciprocal colour algebra (finite algebra)" .leanBank
  , .new "zero-frequency compatibility" .leanBank
  , .new "prime-power / nonunit CRT reduction" .leanBank
  , .new "periodic E1 reduction (complete-sum provider)" .leanConditional
  , .new "E2 outer-multiplier scope theorem" .leanBank
  , .new "outer exponent ledger" .leanBank
  , .new "PairDecompositionProvider (HB identity + dispersion)" .externalProvider
  , .new "ActualCenteredSourceCompositionProvider" .open
  , .new "thin pair theorem" .leanConditional
  , .new "asymptotic Erdős #287" .leanConditional
  , .new "explicit M0" .open
  , .new "finite splice" .open
  , .new "Erdős #287" .open ]

/-- The complete V20 ledger. -/
def v20Ledger : List RowV16 := ResearchBankV19.Ledger.v19Ledger ++ v20New

theorem v20_preserves_v19_ledger :
    v20Ledger.take ResearchBankV19.Ledger.v19Ledger.length = ResearchBankV19.Ledger.v19Ledger ∧
      ∀ r ∈ ResearchBankV19.Ledger.v19Ledger, r ∈ v20Ledger :=
  ⟨List.take_left, fun _ hr => List.mem_append_left _ hr⟩

/-- Look up the class of a V20 row. -/
def clsOf (n : String) : Option SemClass := ((v20New.find? fun r => r.nm = n).bind RowV16.cls?)

/-- **The required final status.** -/
theorem v20_final_status :
    clsOf "V14/V15 infrastructure" = some .leanBank ∧
    clsOf "zero-frequency compatibility" = some .leanBank ∧
    clsOf "prime-power / nonunit CRT reduction" = some .leanBank ∧
    clsOf "outer exponent ledger" = some .leanBank ∧
    clsOf "periodic E1 reduction (complete-sum provider)" = some .leanConditional ∧
    clsOf "ActualCenteredSourceCompositionProvider" = some .open ∧
    clsOf "thin pair theorem" = some .leanConditional ∧
    clsOf "asymptotic Erdős #287" = some .leanConditional ∧
    clsOf "explicit M0" = some .open ∧
    clsOf "finite splice" = some .open ∧
    clsOf "Erdős #287" = some .open := by
  decide

/-- **Erdős #287 is never marked proved in V20.** -/
theorem v20_erdos287_open : ∀ r ∈ v20New, r.nm = "Erdős #287" → r.cls? = some .open := by
  decide

/-- No V20 row puts the composition provider in a proved class. -/
theorem v20_composition_provider_not_proved :
    ∀ r ∈ v20New, r.nm = "ActualCenteredSourceCompositionProvider" →
      r.cls? ≠ some .leanBank ∧ r.cls? ≠ some .leanConditional := by
  decide

end Status
end ResearchBankV20
end Erdos287
