import RequestProject.Erdos287.ResearchBankV19.ActualBranchData
import RequestProject.Erdos287.ResearchBankV19.ActualCenteredCompositionProvider
import RequestProject.Erdos287.ResearchBankV19.CoherentRoots
import RequestProject.Erdos287.ResearchBankV19.E1PeriodicProvider
import RequestProject.Erdos287.ResearchBankV19.E2OuterMultiplier
import RequestProject.Erdos287.ResearchBankV19.HBBranchTaxonomy
import RequestProject.Erdos287.ResearchBankV19.Ledger
import RequestProject.Erdos287.ResearchBankV19.NegativeControls
import RequestProject.Erdos287.ResearchBankV19.NonunitReduction
import RequestProject.Erdos287.ResearchBankV19.OuterCostLedger
import RequestProject.Erdos287.ResearchBankV19.OverlapConductor
import RequestProject.Erdos287.ResearchBankV19.PeriodicReciprocalCompletion
import RequestProject.Erdos287.ResearchBankV19.PrimePowerCRT
import RequestProject.Erdos287.ResearchBankV19.RootClassGram
import RequestProject.Erdos287.ResearchBankV19.ZeroFrequencyCompatibility

/-!
# Erdős #287 — Research Bank V19: axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`#print axioms` for every theorem of Research Bank V19 (66 theorems).  Expected output:
only `propext`, `Classical.choice`, `Quot.sound` (or subsets).
-/

#print axioms Erdos287.ResearchBankV19.BranchData.jointSample_not_in_scope
#print axioms Erdos287.ResearchBankV19.ActualCenteredCompositionProvider.provider_falsifiable
#print axioms Erdos287.ResearchBankV19.CoherentRoots.coherent_zero_mode
#print axioms Erdos287.ResearchBankV19.CoherentRoots.independent_copies_fail
#print axioms Erdos287.ResearchBankV19.CoherentRoots.independent_pair_not_coherent
#print axioms Erdos287.ResearchBankV19.E1Periodic.coeff_periodic
#print axioms Erdos287.ResearchBankV19.E1Periodic.e1_bound
#print axioms Erdos287.ResearchBankV19.E1Periodic.conductor_not_period
#print axioms Erdos287.ResearchBankV19.E2OuterMultiplier.cauchy_outer_absorb
#print axioms Erdos287.ResearchBankV19.E2OuterMultiplier.cauchy_outer_unimodular
#print axioms Erdos287.ResearchBankV19.E2OuterMultiplier.h_multiplier_absorb
#print axioms Erdos287.ResearchBankV19.E2OuterMultiplier.joint_dependence_not_covered
#print axioms Erdos287.ResearchBankV19.E2OuterMultiplier.inner_dependent_outer_fails
#print axioms Erdos287.ResearchBankV19.HBBranchTaxonomy.three_large_impossible
#print axioms Erdos287.ResearchBankV19.HBBranchTaxonomy.three_large_impossible_mul
#print axioms Erdos287.ResearchBankV19.HBBranchTaxonomy.large_count_le_two
#print axioms Erdos287.ResearchBankV19.HBBranchTaxonomy.typeII_partial_sum
#print axioms Erdos287.ResearchBankV19.HBBranchTaxonomy.taxonomy_complete
#print axioms Erdos287.ResearchBankV19.Ledger.v19_preserves_v18_ledger
#print axioms Erdos287.ResearchBankV19.Ledger.v19_erdos287_open
#print axioms Erdos287.ResearchBankV19.Ledger.v19_composition_provider_open
#print axioms Erdos287.ResearchBankV19.NegativeControls.v19_negative_controls
#print axioms Erdos287.ResearchBankV19.NonunitReduction.no_solution_of_not_dvd
#print axioms Erdos287.ResearchBankV19.NonunitReduction.reduce_iff
#print axioms Erdos287.ResearchBankV19.NonunitReduction.reduced_coprime
#print axioms Erdos287.ResearchBankV19.NonunitReduction.reduced_unit_solution
#print axioms Erdos287.ResearchBankV19.OuterCostLedger.sqrt_saving
#print axioms Erdos287.ResearchBankV19.OuterCostLedger.sigma_not_preserved
#print axioms Erdos287.ResearchBankV19.OuterCostLedger.unweighted_divisor_sum_ge
#print axioms Erdos287.ResearchBankV19.OuterCostLedger.not_polylog
#print axioms Erdos287.ResearchBankV19.OuterCostLedger.unweighted_divisor_sum_not_polylog
#print axioms Erdos287.ResearchBankV19.OuterCostLedger.exponent_after_unweighted_sum
#print axioms Erdos287.ResearchBankV19.OuterCostLedger.E1_margin
#print axioms Erdos287.ResearchBankV19.OuterCostLedger.E2_margin
#print axioms Erdos287.ResearchBankV19.OverlapConductor.overlap_conductor_dvd
#print axioms Erdos287.ResearchBankV19.OverlapConductor.prime_power_overlap
#print axioms Erdos287.ResearchBankV19.OverlapConductor.overlap_fixture
#print axioms Erdos287.ResearchBankV19.PeriodicReciprocalCompletion.orth
#print axioms Erdos287.ResearchBankV19.PeriodicReciprocalCompletion.completion_key
#print axioms Erdos287.ResearchBankV19.PeriodicReciprocalCompletion.completion
#print axioms Erdos287.ResearchBankV19.PeriodicReciprocalCompletion.completion_bound
#print axioms Erdos287.ResearchBankV19.PeriodicReciprocalCompletion.Fper_apply
#print axioms Erdos287.ResearchBankV19.PeriodicReciprocalCompletion.periodic_completion_bound
#print axioms Erdos287.ResearchBankV19.PrimePowerCRT.coprime_D1_s1
#print axioms Erdos287.ResearchBankV19.PrimePowerCRT.lcm_eq
#print axioms Erdos287.ResearchBankV19.PrimePowerCRT.crt_phase_reduction
#print axioms Erdos287.ResearchBankV19.PrimePowerCRT.IsPeriod.mul
#print axioms Erdos287.ResearchBankV19.PrimePowerCRT.period_of_dvd
#print axioms Erdos287.ResearchBankV19.PrimePowerCRT.IsPeriod.neg
#print axioms Erdos287.ResearchBankV19.PrimePowerCRT.IsPeriod.mod
#print axioms Erdos287.ResearchBankV19.PrimePowerCRT.leastPeriod_dvd
#print axioms Erdos287.ResearchBankV19.PrimePowerCRT.conductor_dvd
#print axioms Erdos287.ResearchBankV19.PrimePowerCRT.prime_power_fixture
#print axioms Erdos287.ResearchBankV19.RootClassGram.star_char_unit
#print axioms Erdos287.ResearchBankV19.RootClassGram.orth
#print axioms Erdos287.ResearchBankV19.RootClassGram.all_characters
#print axioms Erdos287.ResearchBankV19.RootClassGram.principal_term
#print axioms Erdos287.ResearchBankV19.RootClassGram.totient_ne_zero
#print axioms Erdos287.ResearchBankV19.RootClassGram.root_class_gram
#print axioms Erdos287.ResearchBankV19.ZeroFrequencyCompatibility.compat_necessary
#print axioms Erdos287.ResearchBankV19.ZeroFrequencyCompatibility.cancel_unit
#print axioms Erdos287.ResearchBankV19.ZeroFrequencyCompatibility.crt_exists
#print axioms Erdos287.ResearchBankV19.ZeroFrequencyCompatibility.crt_unique
#print axioms Erdos287.ResearchBankV19.ZeroFrequencyCompatibility.zero_frequency_count
#print axioms Erdos287.ResearchBankV19.ZeroFrequencyCompatibility.phase_at_zero
#print axioms Erdos287.ResearchBankV19.ZeroFrequencyCompatibility.omega_zero_does_not_fix_main_term
