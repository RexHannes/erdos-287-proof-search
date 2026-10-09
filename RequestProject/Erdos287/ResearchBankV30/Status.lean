import RequestProject.Erdos287.ResearchBankV30.TrustedChallenge
import RequestProject.Erdos287.ResearchBankV29.Ledger

/-!
# Erdős #287 — Research Bank V30 §23: success classification

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The four outcomes of task §23, and the one reached (checked by `decide` against the V29 ledger).

* **Not SUCCESS A:** internal rows remain (`ResearchBankV29.Ledger.remaining_internal`).
* **Not SUCCESS B in the strict sense:** the residual internal content is packaged in ONE
  structure (`InternalGlueOwner`) but consists of two derivations (actual-measure majorization
  and nonzero clean realization, the latter containing DIClass membership, kernel realization
  and the pruning contract).
* **SUCCESS C is avoided:** no provider in `MinimalExternalAnalyticProviders` was strengthened;
  the degenerate route (`old_FinalAnalyticProviders_of_degenerate`) that WOULD need a stronger
  tensor provider is recorded but not used.
* **SUCCESS D (reached):** the same-source chain is not established; first mismatch — the
  zero-frequency functional `D0` is not defined from the physical source
  (`SameSourceChain.same_source_not_established`).  The same-weight and same-normalization chains
  DO hold (`same_auxiliary_weight_end_to_end`, `same_normalization_end_to_end`).
-/

namespace Erdos287
namespace ResearchBankV30
namespace Status

open ResearchBankV25.Ledger

/-- The §23 outcomes. -/
inductive Outcome
  | successA_finalBank
  | successB_oneInternalGlue
  | successC_providerMismatch
  | successD_semanticMismatch
  deriving DecidableEq, Repr

/-- The semantic chains of §15–§17. -/
inductive Chain
  | sameSource
  | sameWeight
  | sameNormalization
  deriving DecidableEq, Repr

open Chain

/-- Which chains are established in Lean. -/
def established : Chain → Bool
  | sameSource => false
  | sameWeight => true
  | sameNormalization => true

/-- The outcome reached. -/
def reached : Outcome := Outcome.successD_semanticMismatch

/-- The first failing chain. -/
def firstMismatch : Chain := sameSource

/-- The global-status rows (unchanged from V28). -/
inductive GlobalItem
  | explicitM0
  | finiteSplice
  | globalErdos287
  deriving DecidableEq, Repr

def globalStatus : GlobalItem → StatusClass
  | .explicitM0 => .openProblem
  | .finiteSplice => .openProblem
  | .globalErdos287 => .openProblem

/-- **Final classification** (checked). -/
theorem final_classification :
    reached = Outcome.successD_semanticMismatch ∧ firstMismatch = sameSource ∧
      established sameSource = false ∧ established sameWeight = true ∧
      established sameNormalization = true ∧
      globalStatus .explicitM0 = .openProblem ∧ globalStatus .finiteSplice = .openProblem ∧
      globalStatus .globalErdos287 = .openProblem := by
  decide

/-- **Not SUCCESS A** (checked against the V29 ledger): an internal row is not eliminated. -/
theorem not_successA :
    ResearchBankV29.Ledger.kind .nonzero = .internal ∧
      ResearchBankV29.Ledger.outcome .nonzero ≠ .eliminated := by
  decide

end Status
end ResearchBankV30
end Erdos287
