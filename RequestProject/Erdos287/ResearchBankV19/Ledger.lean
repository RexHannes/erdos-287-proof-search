import RequestProject.Erdos287.ResearchBankV18.Ledger
import RequestProject.Erdos287.ResearchBankV19.NegativeControls

/-!
# Erdős #287 — Research Bank V19: ledger (append-only)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**
-/

namespace Erdos287
namespace ResearchBankV19
namespace Ledger

open ResearchBankV16.Ledger

def v19New : List RowV16 :=
  [ .new "zero-frequency compatibility (necessity, CRT existence/uniqueness, exact count = kappa)"
      .leanBank
  , .new "Omega(0) = 1 implies zero-frequency main term unchanged" .repairedRetired
  , .new "coherent root packets: zero-mode iff n1 = n2 mod g (same assignment)" .leanBank
  , .new "independent-copy root assignments satisfy zero mode" .repairedRetired
  , .new "root-class Gram identity" .leanBank
  , .new "prime-power / overlap CRT reduction and conductor divisibility" .leanBank
  , .new "nonunit coefficient congruence reduction" .leanBank
  , .new "periodic reciprocal completion identity" .leanBank
  , .new "CompleteKloostermanProvider" .externalProvider
  , .new "periodic E1 reduction" .leanConditional
  , .new "conductor E identified with q-period V" .repairedRetired
  , .new "E2 outer-multiplier / own-variable scope theorem" .leanBank
  , .new "arbitrary joint q/h dependence covered" .repairedRetired
  , .new "outer exponent ledger (sqrt halves sigma; eps/2 - delta(2+p))" .leanBank
  , .new "sigma preserved through square root" .repairedRetired
  , .new "fixed J makes unweighted conductor sum polylogarithmic" .repairedRetired
  , .new "local margins E1 17/40000, E2 13/30000 (local only)" .leanBank
  , .new "HB structural taxonomy" .leanBank
  , .new "ActualBranchData record" .leanBank
  , .new "ActualCenteredSourceCompositionProvider (defined, never constructed)" .open
  , .new "Erdős #287" .open ]

def v19Ledger : List RowV16 := ResearchBankV18.Ledger.v18Ledger ++ v19New

theorem v19_preserves_v18_ledger :
    v19Ledger.take ResearchBankV18.Ledger.v18Ledger.length = ResearchBankV18.Ledger.v18Ledger ∧
      ∀ r ∈ ResearchBankV18.Ledger.v18Ledger, r ∈ v19Ledger :=
  ⟨List.take_left, fun _ hr => List.mem_append_left _ hr⟩

theorem v19_erdos287_open : ∀ r ∈ v19New, r.nm = "Erdős #287" → r.cls? = some .open := by
  decide

theorem v19_composition_provider_open :
    .new "ActualCenteredSourceCompositionProvider (defined, never constructed)" .open ∈ v19New := by
  decide

end Ledger
end ResearchBankV19
end Erdos287
