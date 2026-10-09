import RequestProject.Erdos287.ResearchBankV21.Ledger
import RequestProject.Erdos287.ResearchBankV22.IndependentFactorization
import RequestProject.Erdos287.ResearchBankV22.PackingRanges
import RequestProject.Erdos287.ResearchBankV22.RosserCostProvider

/-!
# Erdős #287 — Research Bank V22: ledger (append-only)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The V22 ledger is the complete V21 ledger followed by the V22 rows.  The literal cell-indicator
convolution is `REPAIRED / RETIRED` (replaced by the exact colouring identity).
-/

namespace Erdos287
namespace ResearchBankV22
namespace Ledger

open ResearchBankV16.Ledger

def v22New : List RowV16 :=
  [ .new "exact positive-sieve parameters (vartheta, rho, vartheta0, b_z, s0)" .finiteRegression
  , .new "fixed exceptional prime set E, P_E kept explicit (auxiliary presieve)" .leanBank
  , .new "small-prime Rosser upper weight (beta = 2) satisfies finite contract" .leanBank
  , .new "rounded rough-sieve first-forbidden-prefix positivity" .leanBank
  , .new "completed positive weight Lambda_new^+ = mu_E * beta * ell_rd" .leanBank
  , .new "completed support budget P_E x^rho x^vartheta0" .leanBank
  , .new "exact cell-colouring identity" .leanBank
  , .new "independent coefficient factorization" .leanBank
  , .new "literal cell-indicator convolution (multiplicity 2 at 143)" .repairedRetired
  , .new "packing / range margins" .leanBank
  , .new "normalized-cost factorization and V21 monotonicity for actual weights" .leanBank
  , .new "Rosser scalar asymptotic" .externalProvider
  , .new "prime harmonic tuple rounding estimate" .externalProvider
  , .new "completed cost bound F(s0) + 1/10000 + o(1)" .leanConditional
  , .new "Erdős #287" .open ]

/-- The complete V22 ledger. -/
def v22Ledger : List RowV16 := ResearchBankV21.Ledger.v21Ledger ++ v22New

theorem v22_preserves_v21_ledger :
    v22Ledger.take ResearchBankV21.Ledger.v21Ledger.length = ResearchBankV21.Ledger.v21Ledger ∧
      ∀ r ∈ ResearchBankV21.Ledger.v21Ledger, r ∈ v22Ledger :=
  ⟨List.take_left, fun _ hr => List.mem_append_left _ hr⟩

def clsOf (n : String) : Option SemClass := ((v22New.find? fun r => r.nm = n).bind RowV16.cls?)

theorem v22_final_status :
    clsOf "rounded rough-sieve first-forbidden-prefix positivity" = some .leanBank ∧
    clsOf "completed positive weight Lambda_new^+ = mu_E * beta * ell_rd" = some .leanBank ∧
    clsOf "exact cell-colouring identity" = some .leanBank ∧
    clsOf "independent coefficient factorization" = some .leanBank ∧
    clsOf "packing / range margins" = some .leanBank ∧
    clsOf "Rosser scalar asymptotic" = some .externalProvider ∧
    clsOf "literal cell-indicator convolution (multiplicity 2 at 143)" = some .repairedRetired ∧
    clsOf "Erdős #287" = some .open := by
  decide

theorem v22_erdos287_open : ∀ r ∈ v22New, r.nm = "Erdős #287" → r.cls? = some .open := by
  decide

end Ledger
end ResearchBankV22
end Erdos287
