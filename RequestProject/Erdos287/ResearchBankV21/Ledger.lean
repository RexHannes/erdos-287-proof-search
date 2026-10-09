import RequestProject.Erdos287.ResearchBankV20.Status
import RequestProject.Erdos287.ResearchBankV21.QuadraticDomination
import RequestProject.Erdos287.ResearchBankV21.DensityCounterfixture

/-!
# Erdős #287 — Research Bank V21: ledger (append-only)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The V21 ledger is the complete V20 ledger (V16–V20 rows plus V2–V15 verbatim) followed by the
V21 rows, each carrying exactly one of the six classes.  The V17-style density-invariance
shortcut is recorded as `REPAIRED / RETIRED` with its mod-11 counterfixture.
-/

namespace Erdos287
namespace ResearchBankV21
namespace Ledger

open ResearchBankV16.Ledger

def v21New : List RowV16 :=
  [ .new "V16-V20 (frozen)" .leanBank
  , .new "normalized sieve identity C(q) = sum_S a(S) prod q/(1-q)" .leanBank
  , .new "normalized sieve monotonicity (divisor sums >= 0, signed coefficients)" .leanBank
  , .new "spectator-state local law and envelope h(p) = 1/(p-K+1)" .leanBank
  , .new "conditional density derived from residues" .leanBank
  , .new "spectator-conditioned quadratic domination" .leanBank
  , .new "mod-11 counterfixture: weighted density 4/37 != 1/10" .finiteRegression
  , .new "V17 density-invariance shortcut (spectator square keeps 1/(p-1))" .repairedRetired
  , .new "signed coefficients need not be nonnegative (firewall)" .finiteRegression
  , .new "independence of actual primes" .open
  , .new "Erdős #287" .open ]

/-- The complete V21 ledger. -/
def v21Ledger : List RowV16 := ResearchBankV20.Status.v20Ledger ++ v21New

theorem v21_preserves_v20_ledger :
    v21Ledger.take ResearchBankV20.Status.v20Ledger.length = ResearchBankV20.Status.v20Ledger ∧
      ∀ r ∈ ResearchBankV20.Status.v20Ledger, r ∈ v21Ledger :=
  ⟨List.take_left, fun _ hr => List.mem_append_left _ hr⟩

/-- Look up the class of a V21 row. -/
def clsOf (n : String) : Option SemClass := ((v21New.find? fun r => r.nm = n).bind RowV16.cls?)

theorem v21_final_status :
    clsOf "normalized sieve monotonicity (divisor sums >= 0, signed coefficients)" =
      some .leanBank ∧
    clsOf "spectator-conditioned quadratic domination" = some .leanBank ∧
    clsOf "V17 density-invariance shortcut (spectator square keeps 1/(p-1))" =
      some .repairedRetired ∧
    clsOf "mod-11 counterfixture: weighted density 4/37 != 1/10" = some .finiteRegression ∧
    clsOf "Erdős #287" = some .open := by
  decide

theorem v21_erdos287_open : ∀ r ∈ v21New, r.nm = "Erdős #287" → r.cls? = some .open := by
  decide

end Ledger
end ResearchBankV21
end Erdos287
