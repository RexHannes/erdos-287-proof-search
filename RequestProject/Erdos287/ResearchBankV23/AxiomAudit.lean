import RequestProject.Erdos287.ResearchBankV23.FullLCMPrincipal
import RequestProject.Erdos287.ResearchBankV23.GoodPrimeEulerFactor
import RequestProject.Erdos287.ResearchBankV23.HatApproximationProvider
import RequestProject.Erdos287.ResearchBankV23.Ledger
import RequestProject.Erdos287.ResearchBankV23.PrincipalBudget
import RequestProject.Erdos287.ResearchBankV23.PrincipalCRTMeasure
import RequestProject.Erdos287.ResearchBankV23.PrincipalEulerProvider
import RequestProject.Erdos287.ResearchBankV23.SameWeightPrincipal
import RequestProject.Erdos287.ResearchBankV23.SingularFactors

/-!
# Erdős #287 — Research Bank V23: axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`#print axioms` for every theorem of Research Bank V23 (53 theorems).  Expected output:
only `propext`, `Classical.choice`, `Quot.sound` (or subsets).
-/

#print axioms Erdos287.ResearchBankV23.FullLCMPrincipal.dvd_foldr_lcm
#print axioms Erdos287.ResearchBankV23.FullLCMPrincipal.foldr_lcm_pos
#print axioms Erdos287.ResearchBankV23.FullLCMPrincipal.dvd_fullLCM
#print axioms Erdos287.ResearchBankV23.FullLCMPrincipal.W0_dvd_fullLCM
#print axioms Erdos287.ResearchBankV23.FullLCMPrincipal.s_dvd_fullLCM
#print axioms Erdos287.ResearchBankV23.FullLCMPrincipal.q_dvd_fullLCM
#print axioms Erdos287.ResearchBankV23.FullLCMPrincipal.fullLCM_pos
#print axioms Erdos287.ResearchBankV23.FullLCMPrincipal.principal_prob_fullLCM
#print axioms Erdos287.ResearchBankV23.FullLCMPrincipal.principal_sum_fullLCM
#print axioms Erdos287.ResearchBankV23.GoodPrimeEulerFactor.prod_one_add_indicator
#print axioms Erdos287.ResearchBankV23.GoodPrimeEulerFactor.signedSq_eq
#print axioms Erdos287.ResearchBankV23.GoodPrimeEulerFactor.local_signed_square_average
#print axioms Erdos287.ResearchBankV23.GoodPrimeEulerFactor.eulerFactor_eq_local_average
#print axioms Erdos287.ResearchBankV23.GoodPrimeEulerFactor.signed_square_zero_is_avoidance
#print axioms Erdos287.ResearchBankV23.GoodPrimeEulerFactor.eulerFactor_zero
#print axioms Erdos287.ResearchBankV23.HatApproximationProvider.hat_approximation_eventually_small
#print axioms Erdos287.ResearchBankV23.HatApproximationProvider.hat_not_differentiableAt_zero
#print axioms Erdos287.ResearchBankV23.HatApproximationProvider.hat_ne_differentiable
#print axioms Erdos287.ResearchBankV23.Ledger.v23_preserves_v22_ledger
#print axioms Erdos287.ResearchBankV23.Ledger.v23_final_status
#print axioms Erdos287.ResearchBankV23.Ledger.v23_erdos287_open
#print axioms Erdos287.ResearchBankV23.PrincipalBudget.two_div_diff
#print axioms Erdos287.ResearchBankV23.PrincipalBudget.principal_slack
#print axioms Erdos287.ResearchBankV23.PrincipalBudget.s0_mul_b_z
#print axioms Erdos287.ResearchBankV23.PrincipalBudget.budget_lt_A_C
#print axioms Erdos287.ResearchBankV23.PrincipalBudget.costU_muE
#print axioms Erdos287.ResearchBankV23.PrincipalBudget.cost_LambdaNewPlus_eq
#print axioms Erdos287.ResearchBankV23.PrincipalBudget.F0_mul_g
#print axioms Erdos287.ResearchBankV23.PrincipalBudget.principal_budget_conditional
#print axioms Erdos287.ResearchBankV23.PrincipalBudget.principal_budget_conditional_mul
#print axioms Erdos287.ResearchBankV23.PrincipalBudget.principal_budget_le_A_C
#print axioms Erdos287.ResearchBankV23.PrincipalCRTMeasure.card_fiber_mul
#print axioms Erdos287.ResearchBankV23.PrincipalCRTMeasure.crt_count
#print axioms Erdos287.ResearchBankV23.PrincipalCRTMeasure.principal_prob
#print axioms Erdos287.ResearchBankV23.PrincipalCRTMeasure.principal_Li_identity
#print axioms Erdos287.ResearchBankV23.PrincipalCRTMeasure.crt_count_fixture
#print axioms Erdos287.ResearchBankV23.PrincipalEuler.PrincipalModel.sifted_nonneg
#print axioms Erdos287.ResearchBankV23.PrincipalEuler.zeta_simple_pole_available
#print axioms Erdos287.ResearchBankV23.PrincipalEuler.eulerFactor_zero_value
#print axioms Erdos287.ResearchBankV23.PrincipalEuler.euler_product_at_zero
#print axioms Erdos287.ResearchBankV23.PrincipalEuler.principal_euler_asymptotic
#print axioms Erdos287.ResearchBankV23.PrincipalEuler.singular_chain_normalized
#print axioms Erdos287.ResearchBankV23.PrincipalEuler.same_normalization_sifted_main
#print axioms Erdos287.ResearchBankV23.PrincipalEuler.gConst_pos_le_two
#print axioms Erdos287.ResearchBankV23.SameWeightPrincipal.sum_comm_block
#print axioms Erdos287.ResearchBankV23.SameWeightPrincipal.signed_expansion
#print axioms Erdos287.ResearchBankV23.SameWeightPrincipal.same_weight_principal_bound
#print axioms Erdos287.ResearchBankV23.SameWeightPrincipal.same_weight_principal_bound_LambdaNewPlus
#print axioms Erdos287.ResearchBankV23.SameWeightPrincipal.principalSifted_nonneg
#print axioms Erdos287.ResearchBankV23.SameWeightPrincipal.principal_normalizer_fullLCM
#print axioms Erdos287.ResearchBankV23.SingularFactors.singular_cancellation
#print axioms Erdos287.ResearchBankV23.SingularFactors.ratio_chain_pos
#print axioms Erdos287.ResearchBankV23.SingularFactors.cancellation_needs_nonzero
