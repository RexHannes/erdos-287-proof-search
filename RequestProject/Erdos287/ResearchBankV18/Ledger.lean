import RequestProject.Erdos287.ResearchBankV17.Ledger
import RequestProject.Erdos287.ResearchBankV18.NegativeControls
import RequestProject.Erdos287.ResearchBankV18.ColourConductor

/-!
# Erdős #287 — Research Bank V18: ledger (append-only)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**
-/

namespace Erdos287
namespace ResearchBankV18
namespace Ledger

open ResearchBankV16.Ledger

def v18New : List RowV16 :=
  [ .new "colour-conductor reduction e_D(h c zbar) = e_E(h c0 zbar)" .leanBank
  , .new "character expansion on (ZMod n)^x" .leanBank
  , .new "reciprocal-monomial separation (any number m of factors)" .leanBank
  , .new "number of variables does not enter the scalar cost" .leanBank
  , .new "principal Ramanujan sum = -1" .leanBank
  , .new "M_p^3 <= p^2 and product over squarefree E" .leanBank
  , .new "CRT phase split over coprime moduli" .leanBank
  , .new "GaussMagnitudeProvider" .externalProvider
  , .new "local scalar variation <= M_p (E^(2/3) cost)" .leanConditional
  , .new "D^m residue-cell bound as canonical statement" .repairedRetired
  , .new "MaynardFirstExponentialProvider" .externalProvider
  , .new "MaynardSecondExponentialProvider" .externalProvider
  , .new "multiplier transfer (cost = scalar variation x provider bound)" .leanConditional
  , .new "polarization constants 4 / 16 / 64" .leanBank
  , .new "all actual branches instantiate the Maynard providers" .open
  , .new "Erdős #287" .open ]

def v18Ledger : List RowV16 := ResearchBankV17.Ledger.v17Ledger ++ v18New

theorem v18_preserves_v17_ledger :
    v18Ledger.take ResearchBankV17.Ledger.v17Ledger.length = ResearchBankV17.Ledger.v17Ledger ∧
      ∀ r ∈ ResearchBankV17.Ledger.v17Ledger, r ∈ v18Ledger :=
  ⟨List.take_left, fun _ hr => List.mem_append_left _ hr⟩

theorem v18_erdos287_open : ∀ r ∈ v18New, r.nm = "Erdős #287" → r.cls? = some .open := by
  decide

end Ledger
end ResearchBankV18
end Erdos287
