import RequestProject.Erdos287.ResearchBankV16.BalancedBlowup26
import RequestProject.Erdos287.ResearchBankV16.ConditionalRouteCImplication
import RequestProject.Erdos287.ResearchBankV16.ContactLocalizationC
import RequestProject.Erdos287.ResearchBankV16.Ledger
import RequestProject.Erdos287.ResearchBankV16.MacroGraph26
import RequestProject.Erdos287.ResearchBankV16.RelaxedPairBudget
import RequestProject.Erdos287.ResearchBankV16.RouteCConsumer
import RequestProject.Erdos287.ResearchBankV16.RouteCParameters
import RequestProject.Erdos287.ResearchBankV16.ScopeFirewalls
import RequestProject.Erdos287.ResearchBankV16.Score26

/-!
# Erdős #287 — Research Bank V16: axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`#print axioms` for every theorem of Research Bank V16 (86 theorems).  Expected output:
only `propext`, `Classical.choice`, `Quot.sound` (or subsets).
-/

#print axioms Erdos287.ResearchBankV16.BalancedBlowup26.groupCount_eq
#print axioms Erdos287.ResearchBankV16.BalancedBlowup26.group_val
#print axioms Erdos287.ResearchBankV16.BalancedBlowup26.groupSize_eq_count
#print axioms Erdos287.ResearchBankV16.BalancedBlowup26.groupSize_K
#print axioms Erdos287.ResearchBankV16.BalancedBlowup26.groups_balanced
#print axioms Erdos287.ResearchBankV16.BalancedBlowup26.card_small_groups
#print axioms Erdos287.ResearchBankV16.BalancedBlowup26.groupSize_sum
#print axioms Erdos287.ResearchBankV16.BalancedBlowup26.blowup_adj_iff
#print axioms Erdos287.ResearchBankV16.BalancedBlowup26.no_edge_in_group
#print axioms Erdos287.ResearchBankV16.BalancedBlowup26.blowup_occupied_eight_forces_edge
#print axioms Erdos287.ResearchBankV16.ConditionalRouteCImplication.routeC_eventually_no_counterexample
#print axioms Erdos287.ResearchBankV16.ConditionalRouteCImplication.baseline_provider_falsifiable
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.diffRatio_eq
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.RC_eq
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.RC_lt
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.cC_mul_RC_lt_one
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.cC_mul_RC_buffer_lt_one
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.cC_gt_inv_e
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.log_125_46_lt_one
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.routeB_c_fails_with_RC
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.routeB_buffer_fails
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.cC_lt_c_routeB
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.edge_difference_range_C
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.contact_coeff_ratio_C
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.diff_ratio_of_ranges
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.log_ratio_le_cC
#print axioms Erdos287.ResearchBankV16.ContactLocalizationC.two_hole_contradiction_cC
#print axioms Erdos287.ResearchBankV16.Ledger.old_injective
#print axioms Erdos287.ResearchBankV16.Ledger.v16_preserves_v15_ledger
#print axioms Erdos287.ResearchBankV16.Ledger.v16_erdos287_open
#print axioms Erdos287.ResearchBankV16.Ledger.v16_provider_open
#print axioms Erdos287.ResearchBankV16.MacroGraph26.d26_neg
#print axioms Erdos287.ResearchBankV16.MacroGraph26.d26_zero
#print axioms Erdos287.ResearchBankV16.MacroGraph26.adj_iff
#print axioms Erdos287.ResearchBankV16.MacroGraph26.adj_translate
#print axioms Erdos287.ResearchBankV16.MacroGraph26.off_injective
#print axioms Erdos287.ResearchBankV16.MacroGraph26.off_close
#print axioms Erdos287.ResearchBankV16.MacroGraph26.indep_translate
#print axioms Erdos287.ResearchBankV16.MacroGraph26.indep_card_le_seven_of_zero
#print axioms Erdos287.ResearchBankV16.MacroGraph26.indep_card_le_seven
#print axioms Erdos287.ResearchBankV16.MacroGraph26.arc_indep
#print axioms Erdos287.ResearchBankV16.MacroGraph26.alpha_eq_seven
#print axioms Erdos287.ResearchBankV16.MacroGraph26.col4_classes
#print axioms Erdos287.ResearchBankV16.MacroGraph26.col4_proper
#print axioms Erdos287.ResearchBankV16.MacroGraph26.occupied_eight_forces_edge
#print axioms Erdos287.ResearchBankV16.MacroGraph26.adj_oriented_range
#print axioms Erdos287.ResearchBankV16.RelaxedPairBudget.relaxed_score_positive
#print axioms Erdos287.ResearchBankV16.RelaxedPairBudget.eta_choice
#print axioms Erdos287.ResearchBankV16.RelaxedPairBudget.eventual_score_positive
#print axioms Erdos287.ResearchBankV16.RelaxedPairBudget.baseline_form
#print axioms Erdos287.ResearchBankV16.RouteCConsumer.mem_edges
#print axioms Erdos287.ResearchBankV16.RouteCConsumer.coeff_pos
#print axioms Erdos287.ResearchBankV16.RouteCConsumer.edges_nonempty
#print axioms Erdos287.ResearchBankV16.RouteCConsumer.le_Zmax
#print axioms Erdos287.ResearchBankV16.RouteCConsumer.Zmax_pos
#print axioms Erdos287.ResearchBankV16.RouteCConsumer.rhoC_real
#print axioms Erdos287.ResearchBankV16.RouteCConsumer.window_good
#print axioms Erdos287.ResearchBankV16.RouteCConsumer.sum_occ
#print axioms Erdos287.ResearchBankV16.RouteCConsumer.scoreR_eq
#print axioms Erdos287.ResearchBankV16.RouteCConsumer.score_identity
#print axioms Erdos287.ResearchBankV16.RouteCConsumer.pair_contradiction
#print axioms Erdos287.ResearchBankV16.RouteCConsumer.no_counterexample_of_good_t
#print axioms Erdos287.ResearchBankV16.RouteCParameters.K_pos
#print axioms Erdos287.ResearchBankV16.RouteCParameters.P_eq
#print axioms Erdos287.ResearchBankV16.RouteCParameters.A_C_eq_two_div_theta_add_xi
#print axioms Erdos287.ResearchBankV16.RouteCParameters.A_C_pos
#print axioms Erdos287.ResearchBankV16.RouteCParameters.K_mod_26_aux
#print axioms Erdos287.ResearchBankV16.RouteCParameters.K_mod_26
#print axioms Erdos287.ResearchBankV16.RouteCParameters.marginAt_pos
#print axioms Erdos287.ResearchBankV16.RouteCParameters.routeC_margin_of_certificate
#print axioms Erdos287.ResearchBankV16.RouteCParameters.routeC_margin_pos
#print axioms Erdos287.ResearchBankV16.ScopeFirewalls.routeB_constants_not_imported
#print axioms Erdos287.ResearchBankV16.ScopeFirewalls.certificate_instance
#print axioms Erdos287.ResearchBankV16.ScopeFirewalls.certificate_does_not_give_S0
#print axioms Erdos287.ResearchBankV16.ScopeFirewalls.baseline_provider_not_vacuous
#print axioms Erdos287.ResearchBankV16.ScopeFirewalls.v16_effectivity_firewall
#print axioms Erdos287.ResearchBankV16.Score26.fifty_sub_f
#print axioms Erdos287.ResearchBankV16.Score26.quad_nonneg
#print axioms Erdos287.ResearchBankV16.Score26.f_le_fifty
#print axioms Erdos287.ResearchBankV16.Score26.f_99
#print axioms Erdos287.ResearchBankV16.Score26.f_100
#print axioms Erdos287.ResearchBankV16.Score26.f_zero
#print axioms Erdos287.ResearchBankV16.Score26.score_le_350_of_seven
#print axioms Erdos287.ResearchBankV16.Score26.eight_occupied_of_score_gt
#print axioms Erdos287.ResearchBankV16.Score26.exists_gt_of_weighted_pos
#print axioms Erdos287.ResearchBankV16.Score26.signed_weights_fail
