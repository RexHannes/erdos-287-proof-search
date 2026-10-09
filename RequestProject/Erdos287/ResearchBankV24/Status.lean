import RequestProject.Erdos287.ResearchBankV23.Ledger
import RequestProject.Erdos287.ResearchBankV24.FinalFirewalls

/-!
# Erdős #287 — Research Bank V24: final status ledger (append-only)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The V24 ledger is the complete V23 ledger (hence V2–V23) followed by the final V21–V24 status
rows required by the programme, each carrying exactly one of the six classes
`LEAN BANK`, `LEAN CONDITIONAL`, `EXTERNAL PROVIDER`, `FINITE REGRESSION`,
`REPAIRED / RETIRED`, `OPEN`.  `v24_final_status` checks every required row by `decide`.
-/

namespace Erdos287
namespace ResearchBankV24
namespace Status

open ResearchBankV16.Ledger

def v24New : List RowV16 :=
  [ .new "V16-V20" .leanBank
  , .new "normalized sieve monotonicity" .leanBank
  , .new "spectator-conditioned quadratic domination" .leanBank
  , .new "V17 density-invariance shortcut" .repairedRetired
  , .new "rounded rough-sieve finite positivity" .leanBank
  , .new "completed positive weight" .leanBank
  , .new "exact cell-colouring identity" .leanBank
  , .new "independent coefficient factorization" .leanBank
  , .new "packing/range margins" .leanBank
  , .new "Rosser scalar asymptotic" .externalProvider
  , .new "principal CRT probability" .leanBank
  , .new "singular-factor finite cancellation" .leanBank
  , .new "principal Euler/Mellin asymptotic" .externalProvider
  , .new "exact rational principal slack" .leanBank
  , .new "same-weight signed-principal bound" .leanConditional
  , .new "new completed weight satisfies V16 coefficient contract (algebraic factorization)"
      .leanBank
  , .new "V16 analytic source-class estimate" .externalProvider
  , .new "same-weight actual-measure / tensor decomposition" .externalProvider
  , .new "repaired Route-C pair baseline" .leanConditional
  , .new "asymptotic #287" .leanConditional
  , .new "explicit M0" .open
  , .new "finite splice" .open
  , .new "global Erdős #287" .open ]

/-- The complete V24 ledger. -/
def v24Ledger : List RowV16 := ResearchBankV23.Ledger.v23Ledger ++ v24New

theorem v24_preserves_v23_ledger :
    v24Ledger.take ResearchBankV23.Ledger.v23Ledger.length = ResearchBankV23.Ledger.v23Ledger ∧
      ∀ r ∈ ResearchBankV23.Ledger.v23Ledger, r ∈ v24Ledger :=
  ⟨List.take_left, fun _ hr => List.mem_append_left _ hr⟩

def clsOf (n : String) : Option SemClass := ((v24New.find? fun r => r.nm = n).bind RowV16.cls?)

/-- **The required final status** (section 22 of the programme). -/
theorem v24_final_status :
    clsOf "V16-V20" = some .leanBank ∧
    clsOf "normalized sieve monotonicity" = some .leanBank ∧
    clsOf "spectator-conditioned quadratic domination" = some .leanBank ∧
    clsOf "V17 density-invariance shortcut" = some .repairedRetired ∧
    clsOf "rounded rough-sieve finite positivity" = some .leanBank ∧
    clsOf "completed positive weight" = some .leanBank ∧
    clsOf "exact cell-colouring identity" = some .leanBank ∧
    clsOf "independent coefficient factorization" = some .leanBank ∧
    clsOf "packing/range margins" = some .leanBank ∧
    clsOf "Rosser scalar asymptotic" = some .externalProvider ∧
    clsOf "principal CRT probability" = some .leanBank ∧
    clsOf "singular-factor finite cancellation" = some .leanBank ∧
    clsOf "principal Euler/Mellin asymptotic" = some .externalProvider ∧
    clsOf "exact rational principal slack" = some .leanBank ∧
    clsOf "same-weight signed-principal bound" = some .leanConditional ∧
    clsOf "new completed weight satisfies V16 coefficient contract (algebraic factorization)" =
      some .leanBank ∧
    clsOf "V16 analytic source-class estimate" = some .externalProvider ∧
    clsOf "repaired Route-C pair baseline" = some .leanConditional ∧
    clsOf "asymptotic #287" = some .leanConditional ∧
    clsOf "explicit M0" = some .open ∧
    clsOf "finite splice" = some .open ∧
    clsOf "global Erdős #287" = some .open := by
  decide

/-- The global problem stays `OPEN` in every V21–V24 ledger. -/
theorem v24_global_open :
    clsOf "global Erdős #287" = some .open ∧
      ResearchBankV23.Ledger.clsOf "Erdős #287" = some .open ∧
      ResearchBankV22.Ledger.clsOf "Erdős #287" = some .open ∧
      ResearchBankV21.Ledger.clsOf "Erdős #287" = some .open := by
  decide

/-- No V24 row claims the global theorem as proved. -/
theorem v24_no_global_claim :
    ∀ r ∈ v24New, r.nm = "global Erdős #287" → r.cls? = some .open := by
  decide

end Status
end ResearchBankV24
end Erdos287
