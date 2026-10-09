import RequestProject.Erdos287.ResearchBankV25.Ledger
import RequestProject.Erdos287.ResearchBankV28.PreEffectivityTheorem
import RequestProject.Erdos287.ResearchBankV28.EffectivityFirewall

/-!
# Erdős #287 — Research Bank V28 §18: final ledger

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Status classes are those of `ResearchBankV25.Ledger.StatusClass`
(LEAN BANK / LEAN CONDITIONAL / EXTERNAL PROVIDER / FINITE REGRESSION / REPAIRED-RETIRED / OPEN).
V21–V24 are FROZEN (recorded as the inherited LEAN CONDITIONAL / LEAN BANK chain; not modified).
-/

namespace Erdos287
namespace ResearchBankV28
namespace FinalStatus

open ResearchBankV25.Ledger
open ResearchBankV25.Ledger.StatusClass

/-- The final ledger rows (§18). -/
inductive FinalItem
  | fixedModulusCentering
  | fixedResidueEnergyContraction
  | goodModulusAffineClearing
  | roughHBExactIdentities
  | hbSourceAdapter
  | decoratedCoefficientGrouping
  | representationMoment
  | diSpectralTheorem
  | finiteLabelEnergyGrouping
  | crtColourOrbitCardinality
  | characterFreeColourCost
  | smoothCutoffRecovery
  | globalDAggregationArithmetic
  | cleanNonzeroTheorem
  | sameWeightPrincipal
  | actualPairBaseline
  | preEffectivityAsymptotic
  | parameterArithmetic
  | overclaimFirewalls
  | monolithicSourceClassProvider
  | explicitM0
  | finiteSplice
  | globalErdos287
  deriving DecidableEq, Repr

open FinalItem

def status : FinalItem → StatusClass
  | fixedModulusCentering => leanBank
  | fixedResidueEnergyContraction => leanBank
  | goodModulusAffineClearing => leanBank
  | roughHBExactIdentities => leanBank
  | hbSourceAdapter => leanBank
  | decoratedCoefficientGrouping => leanBank
  | representationMoment => leanConditional
  | diSpectralTheorem => externalProvider
  | finiteLabelEnergyGrouping => leanBank
  | crtColourOrbitCardinality => leanBank
  | characterFreeColourCost => leanConditional
  | smoothCutoffRecovery => leanConditional
  | globalDAggregationArithmetic => leanBank
  | cleanNonzeroTheorem => leanConditional
  | sameWeightPrincipal => leanConditional
  | actualPairBaseline => leanConditional
  | preEffectivityAsymptotic => leanConditional
  | parameterArithmetic => leanBank
  | overclaimFirewalls => finiteRegression
  | monolithicSourceClassProvider => repairedRetired
  | explicitM0 => openProblem
  | finiteSplice => openProblem
  | globalErdos287 => openProblem

/-- **Final classification** (checked by `decide`). -/
theorem final_status :
    status fixedModulusCentering = leanBank ∧ status fixedResidueEnergyContraction = leanBank ∧
    status goodModulusAffineClearing = leanBank ∧ status roughHBExactIdentities = leanBank ∧
    status decoratedCoefficientGrouping = leanBank ∧ status diSpectralTheorem = externalProvider ∧
    status finiteLabelEnergyGrouping = leanBank ∧ status crtColourOrbitCardinality = leanBank ∧
    status characterFreeColourCost = leanConditional ∧
    status cleanNonzeroTheorem = leanConditional ∧ status actualPairBaseline = leanConditional ∧
    status preEffectivityAsymptotic = leanConditional ∧
    status monolithicSourceClassProvider = repairedRetired ∧
    status explicitM0 = openProblem ∧ status finiteSplice = openProblem ∧
    status globalErdos287 = openProblem := by
  decide

/-- The OPEN rows are exactly explicit `M₀`, finite splice and global #287. -/
theorem open_rows : ∀ i, status i = openProblem ↔ i = explicitM0 ∨ i = finiteSplice ∨
    i = globalErdos287 := by
  intro i; cases i <;> simp [status]

end FinalStatus
end ResearchBankV28
end Erdos287
