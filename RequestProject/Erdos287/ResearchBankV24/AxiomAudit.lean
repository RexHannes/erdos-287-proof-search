import RequestProject.Erdos287.ResearchBankV24.ConditionalAsymptotic287
import RequestProject.Erdos287.ResearchBankV24.ConditionalPairBaseline
import RequestProject.Erdos287.ResearchBankV24.FinalFirewalls
import RequestProject.Erdos287.ResearchBankV24.RepairedCompletedSieveProvider
import RequestProject.Erdos287.ResearchBankV24.RepairedRouteCBaseline
import RequestProject.Erdos287.ResearchBankV24.Status

/-!
# Erdős #287 — Research Bank V24: axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`#print axioms` for every theorem of Research Bank V24 (52 theorems).  Expected output:
only `propext`, `Classical.choice`, `Quot.sound` (or subsets).
-/

#print axioms Erdos287.ResearchBankV24.ConditionalAsymptotic287.conditional_asymptotic_287_after_positive_sieve_repair
#print axioms Erdos287.ResearchBankV24.ConditionalPairBaseline.repaired_uses_frozen_normalization
#print axioms Erdos287.ResearchBankV24.ConditionalPairBaseline.conditional_pair_baseline_after_repair
#print axioms Erdos287.ResearchBankV24.FinalFirewalls.fw1_spectator_square_not_raw_density
#print axioms Erdos287.ResearchBankV24.FinalFirewalls.fw2_signed_coefficients
#print axioms Erdos287.ResearchBankV24.FinalFirewalls.fw3_literal_cell_convolution_multiplicity
#print axioms Erdos287.ResearchBankV24.FinalFirewalls.fw4_support_below_three_fifths_no_provider
#print axioms Erdos287.ResearchBankV24.FinalFirewalls.unitCoeff_source
#print axioms Erdos287.ResearchBankV24.FinalFirewalls.evalErr_not_provider
#print axioms Erdos287.ResearchBankV24.FinalFirewalls.fw5_colouring_identity_not_distribution
#print axioms Erdos287.ResearchBankV24.FinalFirewalls.fw6_same_weight_bound_not_V16
#print axioms Erdos287.ResearchBankV24.FinalFirewalls.fw7_score_does_not_construct_baseline
#print axioms Erdos287.ResearchBankV24.FinalFirewalls.fw8_conditional_asymptotic_no_explicit_M0
#print axioms Erdos287.ResearchBankV24.FinalFirewalls.fw9_explicit_M0_required_for_splice
#print axioms Erdos287.ResearchBankV24.RepairedProvider.conv_sum_right
#print axioms Erdos287.ResearchBankV24.RepairedProvider.rep_spec
#print axioms Erdos287.ResearchBankV24.RepairedProvider.cellPattern_iff
#print axioms Erdos287.ResearchBankV24.RepairedProvider.sum_cnt
#print axioms Erdos287.ResearchBankV24.RepairedProvider.pattern_representation
#print axioms Erdos287.ResearchBankV24.RepairedProvider.patterns_card_le
#print axioms Erdos287.ResearchBankV24.RepairedProvider.coloured_source_decomposition
#print axioms Erdos287.ResearchBankV24.RepairedProvider.emb_subtype
#print axioms Erdos287.ResearchBankV24.RepairedProvider.subtype_emb
#print axioms Erdos287.ResearchBankV24.RepairedProvider.emb_subset
#print axioms Erdos287.ResearchBankV24.RepairedProvider.push_pull
#print axioms Erdos287.ResearchBankV24.RepairedProvider.push_oneBounded
#print axioms Erdos287.ResearchBankV24.RepairedProvider.push_supported
#print axioms Erdos287.ResearchBankV24.RepairedProvider.push_conv
#print axioms Erdos287.ResearchBankV24.RepairedProvider.push_sum
#print axioms Erdos287.ResearchBankV24.RepairedProvider.push_source
#print axioms Erdos287.ResearchBankV24.RepairedProvider.push_sourceDecomposition
#print axioms Erdos287.ResearchBankV24.RepairedProvider.pull_supported
#print axioms Erdos287.ResearchBankV24.RepairedProvider.pull_oneBounded
#print axioms Erdos287.ResearchBankV24.RepairedProvider.adm_iff_admGen
#print axioms Erdos287.ResearchBankV24.RepairedProvider.above_insert_max
#print axioms Erdos287.ResearchBankV24.RepairedProvider.admGen_erase_max
#print axioms Erdos287.ResearchBankV24.RepairedProvider.cell_max'_le
#print axioms Erdos287.ResearchBankV24.RepairedProvider.cnt_erase_eq
#print axioms Erdos287.ResearchBankV24.RepairedProvider.card_eq_sum_cnt
#print axioms Erdos287.ResearchBankV24.RepairedProvider.admGen_count
#print axioms Erdos287.ResearchBankV24.RepairedProvider.ellRd_countDetermined
#print axioms Erdos287.ResearchBankV24.RepairedProvider.new_completed_weight_matches_V16_contract
#print axioms Erdos287.ResearchBankV24.RepairedProvider.rounded_completed_weight_matches_V16_contract
#print axioms Erdos287.ResearchBankV24.RepairedProvider.distribution_error_small
#print axioms Erdos287.ResearchBankV24.RepairedProvider.small_prime_weight_constructed
#print axioms Erdos287.ResearchBankV24.RepairedRouteCBaseline.ellRd_congr
#print axioms Erdos287.ResearchBankV24.RepairedRouteCBaseline.lamFam_source_decomposition
#print axioms Erdos287.ResearchBankV24.RepairedRouteCBaseline.repaired_routeC_baseline_of_providers
#print axioms Erdos287.ResearchBankV24.Status.v24_preserves_v23_ledger
#print axioms Erdos287.ResearchBankV24.Status.v24_final_status
#print axioms Erdos287.ResearchBankV24.Status.v24_global_open
#print axioms Erdos287.ResearchBankV24.Status.v24_no_global_claim
