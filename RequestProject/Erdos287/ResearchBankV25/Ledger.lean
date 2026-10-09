import RequestProject.Erdos287.ResearchBankV25.GoodModulusClearing
import RequestProject.Erdos287.ResearchBankV25.LocalizationContract
import RequestProject.Erdos287.ResearchBankV25.Counterfixtures

/-!
# Erdős #287 — Research Bank V25: ledger

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The six admissible status classes (§2 of the V25–V28 request) are the constructors of
`StatusClass`; no other status word is used.  `v25_final_status` checks the classification by
`decide`, and `v25_bank_certificate` ties the LEAN BANK rows to the actual kernel theorems.
-/

namespace Erdos287
namespace ResearchBankV25
namespace Ledger

/-- The only admissible status classes. -/
inductive StatusClass
  | leanBank
  | leanConditional
  | externalProvider
  | finiteRegression
  | repairedRetired
  | openProblem
  deriving DecidableEq, Repr

/-- The V25 ledger rows. -/
inductive V25Item
  | fixedModulusCentering
  | correctionTermNeeded
  | correctionSplit
  | maskedSWProvider
  | correctionAggregation
  | conditionedResidueEnergy
  | overlapFibres
  | coprimeLocalizedEnergy
  | divisorReindexing
  | locBound
  | bdhEnergyProvider
  | zeroFrequencyLocalized
  | goodModulusClearing
  | residueRestrictionSW
  | slopeUnitDestruction
  | erdos287Global
  deriving DecidableEq, Repr

open StatusClass V25Item

/-- The V25 classification. -/
def status : V25Item → StatusClass
  | fixedModulusCentering => leanBank
  | correctionTermNeeded => finiteRegression
  | correctionSplit => leanBank
  | maskedSWProvider => externalProvider
  | correctionAggregation => leanConditional
  | conditionedResidueEnergy => leanBank
  | overlapFibres => leanBank
  | coprimeLocalizedEnergy => leanBank
  | divisorReindexing => leanBank
  | locBound => leanBank
  | bdhEnergyProvider => externalProvider
  | zeroFrequencyLocalized => leanConditional
  | goodModulusClearing => leanBank
  | residueRestrictionSW => repairedRetired
  | slopeUnitDestruction => repairedRetired
  | erdos287Global => openProblem

theorem v25_final_status :
    status fixedModulusCentering = leanBank ∧ status conditionedResidueEnergy = leanBank ∧
    status goodModulusClearing = leanBank ∧ status maskedSWProvider = externalProvider ∧
    status bdhEnergyProvider = externalProvider ∧
    status zeroFrequencyLocalized = leanConditional ∧
    status residueRestrictionSW = repairedRetired ∧ status slopeUnitDestruction = repairedRetired ∧
    status erdos287Global = openProblem := by decide

/-- The LEAN BANK / FINITE REGRESSION rows are backed by kernel theorems. -/
theorem v25_bank_certificate :
    ¬ FixedModulusCentering.CorrectionDeletable ∧
    (Counterfixtures.Balanced 3 (Finset.Icc 1 6) (fun _ => 1) ∧
      ¬ Counterfixtures.Balanced 3 (Finset.Icc 1 6)
        (FixedResidueEnergy.alphaLoc (f := 3) (fun _ => 1) 1)) ∧
    (∀ Ai Aj t : ℤ, Aj * (Ai * t + 1) - (Aj - Ai) = Ai * (Aj * t + 1)) :=
  ⟨FixedModulusCentering.correction_term_needed, Counterfixtures.residue_restriction_breaks_SW,
    GoodModulusClearing.clearing_identity_j⟩

end Ledger
end ResearchBankV25
end Erdos287
