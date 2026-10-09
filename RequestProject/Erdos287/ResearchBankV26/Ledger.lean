import RequestProject.Erdos287.ResearchBankV25.Ledger
import RequestProject.Erdos287.ResearchBankV26.HBBranchCoverage
import RequestProject.Erdos287.ResearchBankV26.SingletonBins
import RequestProject.Erdos287.ResearchBankV26.ProductIntervalBoxes
import RequestProject.Erdos287.ResearchBankV26.BoundaryBudget

/-!
# Erdős #287 — Research Bank V26: ledger

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Status classes are those of `ResearchBankV25.Ledger.StatusClass`.
-/

namespace Erdos287
namespace ResearchBankV26
namespace Ledger

open ResearchBankV25.Ledger
open ResearchBankV25.Ledger.StatusClass

/-- The V26 ledger rows. -/
inductive V26Item
  | roughMuIdentity
  | roughOneIdentity
  | truncationSplit
  | truncationErrorBound
  | smoothTailProvider
  | truncationConditional
  | heathBrownIdentity
  | heathBrownK3
  | singletonPadding
  | sourceTypes
  | roughNotSW
  | dyadicPartition
  | interiorRectangular
  | boxDecomposition
  | productBoundaryProvider
  | productBoxingConditional
  | boundaryBudget
  | branchTrichotomy
  | trichotomyThresholdRegression
  | sourceLevelCoverage
  | erdos287Global
  deriving DecidableEq, Repr

open V26Item

def status : V26Item → StatusClass
  | roughMuIdentity => leanBank
  | roughOneIdentity => leanBank
  | truncationSplit => leanBank
  | truncationErrorBound => leanBank
  | smoothTailProvider => externalProvider
  | truncationConditional => leanConditional
  | heathBrownIdentity => leanBank
  | heathBrownK3 => leanBank
  | singletonPadding => leanBank
  | sourceTypes => leanBank
  | roughNotSW => finiteRegression
  | dyadicPartition => leanBank
  | interiorRectangular => leanBank
  | boxDecomposition => leanBank
  | productBoundaryProvider => externalProvider
  | productBoxingConditional => leanConditional
  | boundaryBudget => leanBank
  | branchTrichotomy => leanBank
  | trichotomyThresholdRegression => finiteRegression
  | sourceLevelCoverage => leanBank
  | erdos287Global => openProblem

theorem v26_final_status :
    status roughMuIdentity = leanBank ∧ status heathBrownIdentity = leanBank ∧
    status sourceLevelCoverage = leanBank ∧ status smoothTailProvider = externalProvider ∧
    status productBoundaryProvider = externalProvider ∧
    status productBoxingConditional = leanConditional ∧ status erdos287Global = openProblem := by
  decide

/-- The central LEAN BANK rows are backed by kernel theorems. -/
theorem v26_bank_certificate (z : ℕ) :
    (ArithmeticFunction.moebius : ArithmeticFunction ℤ).pmul (RoughConvolution.R z) =
        ArithmeticFunction.moebius * RoughConvolution.H z ∧
    RoughConvolution.R z = (ArithmeticFunction.zeta : ArithmeticFunction ℤ) *
        (ArithmeticFunction.moebius : ArithmeticFunction ℤ).pmul (RoughConvolution.H z) :=
  ⟨RoughConvolution.rough_mu_identity z, RoughConvolution.rough_one_identity z⟩

end Ledger
end ResearchBankV26
end Erdos287
