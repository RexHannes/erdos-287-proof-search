import RequestProject.Erdos287.ResearchBankV22.Ledger
import RequestProject.Erdos287.ResearchBankV23.PrincipalCRTMeasure
import RequestProject.Erdos287.ResearchBankV23.FullLCMPrincipal
import RequestProject.Erdos287.ResearchBankV23.HatApproximationProvider
import RequestProject.Erdos287.ResearchBankV23.PrincipalBudget

/-!
# Erdős #287 — Research Bank V23: ledger (append-only)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The V23 ledger is the complete V22 ledger followed by the V23 rows.
-/

namespace Erdos287
namespace ResearchBankV23
namespace Ledger

open ResearchBankV16.Ledger

def v23New : List RowV16 :=
  [ .new "principal CRT probability phi(A W0)/phi(A L0) * unit indicator" .leanBank
  , .new "full-lcm principal normalizer L0 = lcm(W0, s, q_1..q_r)" .leanBank
  , .new "singular-factor finite cancellation" .leanBank
  , .new "good-prime Euler factor = local signed-square average" .leanBank
  , .new "signed expansion of the principal functional" .leanBank
  , .new "same-weight signed-principal bound M_new <= C(h) * sifted" .leanBank
  , .new "principal Euler/Mellin asymptotic" .externalProvider
  , .new "hat-reference approximation E|A-B|^2 <= C (log x)^-(K+26)" .externalProvider
  , .new "hat interpolant is not a smooth cutoff (firewall)" .leanBank
  , .new "same normalization sifted main term e^-gamma/b_z L(F)/I" .leanConditional
  , .new "exact rational principal slack" .leanBank
  , .new "principal budget M_new <= (2/vartheta0 + 1/5000) W_F + eps" .leanConditional
  , .new "same-weight signed-principal bound (analytic form)" .leanConditional
  , .new "V16 analytic source-class theorem" .externalProvider
  , .new "Erdős #287" .open ]

/-- The complete V23 ledger. -/
def v23Ledger : List RowV16 := ResearchBankV22.Ledger.v22Ledger ++ v23New

theorem v23_preserves_v22_ledger :
    v23Ledger.take ResearchBankV22.Ledger.v22Ledger.length = ResearchBankV22.Ledger.v22Ledger ∧
      ∀ r ∈ ResearchBankV22.Ledger.v22Ledger, r ∈ v23Ledger :=
  ⟨List.take_left, fun _ hr => List.mem_append_left _ hr⟩

def clsOf (n : String) : Option SemClass := ((v23New.find? fun r => r.nm = n).bind RowV16.cls?)

theorem v23_final_status :
    clsOf "principal CRT probability phi(A W0)/phi(A L0) * unit indicator" = some .leanBank ∧
    clsOf "singular-factor finite cancellation" = some .leanBank ∧
    clsOf "principal Euler/Mellin asymptotic" = some .externalProvider ∧
    clsOf "exact rational principal slack" = some .leanBank ∧
    clsOf "same-weight signed-principal bound (analytic form)" = some .leanConditional ∧
    clsOf "Erdős #287" = some .open := by
  decide

theorem v23_erdos287_open : ∀ r ∈ v23New, r.nm = "Erdős #287" → r.cls? = some .open := by
  decide

end Ledger
end ResearchBankV23
end Erdos287
