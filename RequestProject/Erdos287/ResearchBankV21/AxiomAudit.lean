import RequestProject.Erdos287.ResearchBankV21.ConditionalDensity
import RequestProject.Erdos287.ResearchBankV21.DensityCounterfixture
import RequestProject.Erdos287.ResearchBankV21.FiniteSieveSetup
import RequestProject.Erdos287.ResearchBankV21.Ledger
import RequestProject.Erdos287.ResearchBankV21.NormalizedSieveMonotonicity
import RequestProject.Erdos287.ResearchBankV21.QuadraticDomination
import RequestProject.Erdos287.ResearchBankV21.SpectatorStates

/-!
# Erdős #287 — Research Bank V21: axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`#print axioms` for every theorem of Research Bank V21 (43 theorems).  Expected output:
only `propext`, `Classical.choice`, `Quot.sound` (or subsets).
-/

#print axioms Erdos287.ResearchBankV21.ConditionalDensity.card_state_some
#print axioms Erdos287.ResearchBankV21.ConditionalDensity.card_state_none
#print axioms Erdos287.ResearchBankV21.ConditionalDensity.card_none_and_Lj
#print axioms Erdos287.ResearchBankV21.ConditionalDensity.card_some_and_Lj
#print axioms Erdos287.ResearchBankV21.ConditionalDensity.repaired_law_from_residues
#print axioms Erdos287.ResearchBankV21.DensityCounterfixture.support_eq
#print axioms Erdos287.ResearchBankV21.DensityCounterfixture.raw_density
#print axioms Erdos287.ResearchBankV21.DensityCounterfixture.weighted_density
#print axioms Erdos287.ResearchBankV21.DensityCounterfixture.spectator_square_density_not_invariant
#print axioms Erdos287.ResearchBankV21.DensityCounterfixture.counterfixture_within_envelope
#print axioms Erdos287.ResearchBankV21.FiniteSieveSetup.sum_supset_prod
#print axioms Erdos287.ResearchBankV21.FiniteSieveSetup.sum_divSum_mul
#print axioms Erdos287.ResearchBankV21.Ledger.v21_preserves_v20_ledger
#print axioms Erdos287.ResearchBankV21.Ledger.v21_final_status
#print axioms Erdos287.ResearchBankV21.Ledger.v21_erdos287_open
#print axioms Erdos287.ResearchBankV21.NormalizedSieveMonotonicity.normCost_eq_sum_divSum
#print axioms Erdos287.ResearchBankV21.NormalizedSieveMonotonicity.odds_mono
#print axioms Erdos287.ResearchBankV21.NormalizedSieveMonotonicity.odds_nonneg
#print axioms Erdos287.ResearchBankV21.NormalizedSieveMonotonicity.normCost_mono
#print axioms Erdos287.ResearchBankV21.NormalizedSieveMonotonicity.normCost_nonneg
#print axioms Erdos287.ResearchBankV21.NormalizedSieveMonotonicity.unit_univ
#print axioms Erdos287.ResearchBankV21.NormalizedSieveMonotonicity.unit_powerset
#print axioms Erdos287.ResearchBankV21.NormalizedSieveMonotonicity.signed_coefficient_nonneg_divSum
#print axioms Erdos287.ResearchBankV21.NormalizedSieveMonotonicity.monotonicity_needs_divSum_nonneg
#print axioms Erdos287.ResearchBankV21.QuadraticDomination.patternProb_nonneg
#print axioms Erdos287.ResearchBankV21.QuadraticDomination.patternProb_sum
#print axioms Erdos287.ResearchBankV21.QuadraticDomination.condExp_sieve
#print axioms Erdos287.ResearchBankV21.QuadraticDomination.condProb_sifted
#print axioms Erdos287.ResearchBankV21.QuadraticDomination.condExp_eq_normCost_mul
#print axioms Erdos287.ResearchBankV21.QuadraticDomination.condProb_sifted_nonneg
#print axioms Erdos287.ResearchBankV21.QuadraticDomination.condExp_le_envelope
#print axioms Erdos287.ResearchBankV21.QuadraticDomination.quadratic_domination
#print axioms Erdos287.ResearchBankV21.QuadraticDomination.quadratic_domination_signed_tensor
#print axioms Erdos287.ResearchBankV21.QuadraticDomination.spectatorLaw_nonneg
#print axioms Erdos287.ResearchBankV21.QuadraticDomination.quadratic_domination_spectator
#print axioms Erdos287.ResearchBankV21.SpectatorStates.stateProb_sum_one
#print axioms Erdos287.ResearchBankV21.SpectatorStates.stateProb_nonneg
#print axioms Erdos287.ResearchBankV21.SpectatorStates.condDensity_le_envelope
#print axioms Erdos287.ResearchBankV21.SpectatorStates.condDensity_nonneg
#print axioms Erdos287.ResearchBankV21.SpectatorStates.envelope_lt_one
#print axioms Erdos287.ResearchBankV21.SpectatorStates.envelope_eq
#print axioms Erdos287.ResearchBankV21.SpectatorStates.average_condDensity
#print axioms Erdos287.ResearchBankV21.SpectatorStates.envelope_gt_raw
