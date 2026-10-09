import RequestProject.Erdos287.ResearchBankV25.Ledger
import RequestProject.Erdos287.ResearchBankV27.CleanNonzero
import RequestProject.Erdos287.ResearchBankV27.OuterInnerSeparation

/-!
# Erdős #287 — Research Bank V27: ledger

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Status classes are those of `ResearchBankV25.Ledger.StatusClass`.
-/

namespace Erdos287
namespace ResearchBankV27
namespace Ledger

open ResearchBankV25.Ledger
open ResearchBankV25.Ledger.StatusClass

/-- The V27 ledger rows. -/
inductive V27Item
  | cleanDomain
  | rangeExponentArithmetic
  | outerInnerFirewall
  | productCutoffSeparation
  | productCutoffFourierProvider
  | commonCauchy
  | cauchyDirectionRegression
  | groupedCoefficient
  | representationBounds
  | diagonalRepresentationCount
  | representationMomentProvider
  | diSpectralProvider
  | decoratedMasterBound
  | decoratedExponentSavings
  | finiteLabelEnergy
  | labelEnergyRegression
  | crtColourOrbit
  | characterFreeColourCost
  | reciprocityAlgebra
  | schwartzFrequencyProvider
  | frequencyCapProvider
  | smoothRecoveryProvider
  | smoothCutoffRecovery
  | exactOneOverD
  | liftedScaleRegression
  | divisorSumProvider
  | globalDAggregationArithmetic
  | cleanNonzeroTheorem
  | erdos287Global
  deriving DecidableEq, Repr

open V27Item

def status : V27Item → StatusClass
  | cleanDomain => leanBank
  | rangeExponentArithmetic => leanBank
  | outerInnerFirewall => leanBank
  | productCutoffSeparation => leanBank
  | productCutoffFourierProvider => externalProvider
  | commonCauchy => leanBank
  | cauchyDirectionRegression => finiteRegression
  | groupedCoefficient => leanBank
  | representationBounds => leanBank
  | diagonalRepresentationCount => leanBank
  | representationMomentProvider => externalProvider
  | diSpectralProvider => externalProvider
  | decoratedMasterBound => leanConditional
  | decoratedExponentSavings => leanBank
  | finiteLabelEnergy => leanBank
  | labelEnergyRegression => finiteRegression
  | crtColourOrbit => leanBank
  | characterFreeColourCost => leanConditional
  | reciprocityAlgebra => leanBank
  | schwartzFrequencyProvider => externalProvider
  | frequencyCapProvider => externalProvider
  | smoothRecoveryProvider => externalProvider
  | smoothCutoffRecovery => leanConditional
  | exactOneOverD => leanBank
  | liftedScaleRegression => finiteRegression
  | divisorSumProvider => externalProvider
  | globalDAggregationArithmetic => leanBank
  | cleanNonzeroTheorem => leanConditional
  | erdos287Global => openProblem

theorem v27_final_status :
    status groupedCoefficient = leanBank ∧ status finiteLabelEnergy = leanBank ∧
    status crtColourOrbit = leanBank ∧ status diSpectralProvider = externalProvider ∧
    status characterFreeColourCost = leanConditional ∧
    status smoothCutoffRecovery = leanConditional ∧
    status globalDAggregationArithmetic = leanBank ∧
    status cleanNonzeroTheorem = leanConditional ∧ status erdos287Global = openProblem := by
  decide

/-- Kernel certificates behind central LEAN BANK rows. -/
theorem v27_bank_certificate :
    (∀ (D t : ℕ) [NeZero D], (CRTColourOrbit.orbit D t).card = Nat.totient (CRTColourOrbit.ED D t)) ∧
    GlobalConductorSum.eta - 3 * GlobalConductorSum.sigma / 2 = 347 / 418000 ∧
    (GlobalConductorSum.eta - 3 * GlobalConductorSum.sigma / 2) / 2 = 347 / 836000 :=
  ⟨fun D t _ => CRTColourOrbit.orbit_card D t, GlobalConductorSum.clean_energy_saving.1,
    GlobalConductorSum.clean_discrepancy_saving.1⟩

end Ledger
end ResearchBankV27
end Erdos287
