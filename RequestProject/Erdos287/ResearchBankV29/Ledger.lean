import RequestProject.Erdos287.ResearchBankV25.Ledger
import RequestProject.Erdos287.ResearchBankV29.ProviderElimination

/-!
# Erdős #287 — Research Bank V29: ledger

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

One row per V28 bundle field (plus the V29 task items), with (a) its status class
(`ResearchBankV25.Ledger.StatusClass`) and (b) its INTERNAL / EXTERNAL classification and whether
V29 eliminated it.  Checked by `decide`.
-/

namespace Erdos287
namespace ResearchBankV29
namespace Ledger

open ResearchBankV25.Ledger
open ResearchBankV25.Ledger.StatusClass

/-- Classification of an assumption (task §2). -/
inductive Kind
  | internal
  | external
  | finiteCertified
  deriving DecidableEq, Repr

/-- Outcome of the V29 elimination attempt. -/
inductive Outcome
  | eliminated
  | keptExternal
  | keptInternalGlue
  | isolatedCertificate
  deriving DecidableEq, Repr

/-- The rows. -/
inductive V29Item
  | rosser | tuple | euler | hat | di | zeroFreq | oneLarge | twoLarge | boundary
  | nonzero | tensor | s1 | cert
  | sameNormalization | sameWeight | scoreFormula | pruningContract | diClassMembership
  | kernelRealization
  deriving DecidableEq, Repr

open V29Item Kind Outcome

def kind : V29Item → Kind
  | rosser => external | tuple => external | euler => external | hat => external
  | di => external | zeroFreq => external | oneLarge => external | twoLarge => external
  | boundary => external | nonzero => internal | tensor => internal | s1 => external
  | cert => finiteCertified | sameNormalization => internal | sameWeight => internal
  | scoreFormula => internal | pruningContract => internal | diClassMembership => internal
  | kernelRealization => internal

def outcome : V29Item → Outcome
  | rosser => keptExternal | tuple => keptExternal | euler => keptExternal
  | hat => keptExternal | di => keptExternal | zeroFreq => keptExternal
  | oneLarge => keptExternal | twoLarge => keptExternal | boundary => keptExternal
  | nonzero => keptInternalGlue | tensor => keptInternalGlue | s1 => keptExternal
  | cert => isolatedCertificate | sameNormalization => eliminated | sameWeight => eliminated
  | scoreFormula => eliminated | pruningContract => keptInternalGlue
  | diClassMembership => keptInternalGlue | kernelRealization => keptInternalGlue

def status : V29Item → StatusClass
  | rosser => externalProvider | tuple => externalProvider | euler => externalProvider
  | hat => externalProvider | di => externalProvider | zeroFreq => externalProvider
  | oneLarge => externalProvider | twoLarge => externalProvider
  | boundary => externalProvider | nonzero => openProblem | tensor => openProblem
  | s1 => externalProvider | cert => externalProvider | sameNormalization => leanBank
  | sameWeight => leanBank | scoreFormula => leanBank | pruningContract => openProblem
  | diClassMembership => openProblem | kernelRealization => openProblem

/-- **No internal row is kept as an external provider** (checked). -/
theorem internal_not_external : ∀ i, kind i = internal → outcome i ≠ keptExternal := by
  intro i; cases i <;> decide

/-- **The internal rows NOT eliminated are exactly the glue-owner rows** (checked). -/
theorem remaining_internal :
    ∀ i, (kind i = internal ∧ outcome i ≠ eliminated) ↔
      i = nonzero ∨ i = tensor ∨ i = pruningContract ∨ i = diClassMembership ∨
        i = kernelRealization := by
  intro i; cases i <;> decide

/-- The certificate is isolated, not an analytic provider (checked). -/
theorem cert_isolated : kind cert = finiteCertified ∧ outcome cert = isolatedCertificate := by
  decide

end Ledger
end ResearchBankV29
end Erdos287
