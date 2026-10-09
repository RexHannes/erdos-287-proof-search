import RequestProject.Erdos287.ResearchBankV8.ActiveResidueDP
import RequestProject.Erdos287.ResearchBankV8.CertificateInterval
import RequestProject.Erdos287.ResearchBankV8.ExactEntrySystem
import RequestProject.Erdos287.ResearchBankV8.GoodM
import RequestProject.Erdos287.ResearchBankV8.Ledger
import RequestProject.Erdos287.ResearchBankV8.RigidK2
import RequestProject.Erdos287.ResearchBankV8.RoughWindow
import RequestProject.Erdos287.ResearchBankV8.Saturation
import RequestProject.Erdos287.ResearchBankV8.TernaryBlocker
import RequestProject.Erdos287.ResearchBankV8.VirtualEdge
import RequestProject.Erdos287.ResearchBankV8.WeakCutoffSeed
import RequestProject.Erdos287.ResearchBankV8.WholeParentCap

/-!
# Research Bank V8 — axiom audit

`#print axioms` for every theorem of the V8 layer.  Expected output: only `propext`,
`Classical.choice`, `Quot.sound` (or no axioms at all).  No `sorryAx`, no native-evaluation
axiom, no custom research axiom.
-/

#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.wsum_append
#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.noAdjB_cons
#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.noAdjB_append
#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.dvd_add_iff_of_emod_eq
#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.feasible_eq_of_state_eq
#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.wsum_zero_of_after
#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.forget_owner_of_final_zero
#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.owner_final_nonzero_infeasible
#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.forget_before_final_unsound
#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.forget_nonzero_unsound
#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.same_bit_not_same_continuation
#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.boundary_bit_only_not_exact
#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.mem_allWords
#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.boundedSolve_unsat_sound
#print axioms Erdos287.ResearchBankV8.ActiveResidueDP.resource_exhaustion_not_unsat
#print axioms Erdos287.ResearchBankV8.CertificateInterval.Icc_eq_Icc_iff
#print axioms Erdos287.ResearchBankV8.CertificateInterval.ceilDiv3_eq_iff
#print axioms Erdos287.ResearchBankV8.CertificateInterval.div_eq_iff'
#print axioms Erdos287.ResearchBankV8.CertificateInterval.certInterval_eq_iff
#print axioms Erdos287.ResearchBankV8.CertificateInterval.mem_all_windows_iff
#print axioms Erdos287.ResearchBankV8.CertificateInterval.window_inter
#print axioms Erdos287.ResearchBankV8.CertificateInterval.ValidSource.certInterval_eq
#print axioms Erdos287.ResearchBankV8.CertificateInterval.window_examples
#print axioms Erdos287.ResearchBankV8.ExactEntrySystem.PInt.int
#print axioms Erdos287.ResearchBankV8.ExactEntrySystem.PInt.add
#print axioms Erdos287.ResearchBankV8.ExactEntrySystem.PInt.neg
#print axioms Erdos287.ResearchBankV8.ExactEntrySystem.PInt.sum
#print axioms Erdos287.ResearchBankV8.ExactEntrySystem.PInt.add_iff
#print axioms Erdos287.ResearchBankV8.ExactEntrySystem.PInt.pow_div
#print axioms Erdos287.ResearchBankV8.ExactEntrySystem.PInt.term_of_not_dvd
#print axioms Erdos287.ResearchBankV8.ExactEntrySystem.row_pint_iff
#print axioms Erdos287.ResearchBankV8.ExactEntrySystem.lcm_decomp
#print axioms Erdos287.ResearchBankV8.ExactEntrySystem.image_rowSet
#print axioms Erdos287.ResearchBankV8.ExactEntrySystem.pLocal_entry_iff_row_congruence
#print axioms Erdos287.ResearchBankV8.ExactEntrySystem.top_digit_insufficient
#print axioms Erdos287.ResearchBankV8.ExactEntrySystem.mod_p_not_sufficient
#print axioms Erdos287.ResearchBankV8.GoodM.entrySat_count_eq
#print axioms Erdos287.ResearchBankV8.GoodM.inter_biUnion_card_le
#print axioms Erdos287.ResearchBankV8.GoodM.exists_good_source_of_first_moment
#print axioms Erdos287.ResearchBankV8.GoodM.card_pos_of_first_moment
#print axioms Erdos287.ResearchBankV8.GoodM.completeness_not_automatic
#print axioms Erdos287.ResearchBankV8.Ledger.epochV8_chronology
#print axioms Erdos287.ResearchBankV8.Ledger.ofV7_injective
#print axioms Erdos287.ResearchBankV8.Ledger.v7_classifications_preserved
#print axioms Erdos287.ResearchBankV8.Ledger.v8_no_closed
#print axioms Erdos287.ResearchBankV8.Ledger.v8_erdos287_open
#print axioms Erdos287.ResearchBankV8.Ledger.v8_proved_implies_kernel
#print axioms Erdos287.ResearchBankV8.Ledger.v8_record_rows_not_proved
#print axioms Erdos287.ResearchBankV8.Ledger.v8_external_not_proved
#print axioms Erdos287.ResearchBankV8.Ledger.v8_cap_killed_entry_open
#print axioms Erdos287.ResearchBankV8.Ledger.killedSufficient_ne_false
#print axioms Erdos287.ResearchBankV8.Ledger.superseded_ne_false
#print axioms Erdos287.ResearchBankV8.RigidK2.rigid_iff_capacity_zero
#print axioms Erdos287.ResearchBankV8.RigidK2.rigid_row_forces_zero
#print axioms Erdos287.ResearchBankV8.RigidK2.k2_forces_adjacent_zeros
#print axioms Erdos287.ResearchBankV8.RigidK2.k2_unsat
#print axioms Erdos287.ResearchBankV8.RigidK2.row_alone_compatible
#print axioms Erdos287.ResearchBankV8.RigidK2.contact_unique
#print axioms Erdos287.ResearchBankV8.RigidK2.rigid_row_avoids_selected_endpoint
#print axioms Erdos287.ResearchBankV8.RigidK2.k2_unsat_infinitely_often_of_supply
#print axioms Erdos287.ResearchBankV8.RigidK2.k2_instance
#print axioms Erdos287.ResearchBankV8.RigidK2.rigid_not_positive_capacity
#print axioms Erdos287.ResearchBankV8.RigidK2.k2_does_not_refute_positive_capacity
#print axioms Erdos287.ResearchBankV8.RoughWindow.coprime_of_rough
#print axioms Erdos287.ResearchBankV8.RoughWindow.rough_multiplier_unique
#print axioms Erdos287.ResearchBankV8.RoughWindow.rough_supports_disjoint
#print axioms Erdos287.ResearchBankV8.RoughWindow.support_card
#print axioms Erdos287.ResearchBankV8.RoughWindow.rough_labels_not_pairwise_coprime
#print axioms Erdos287.ResearchBankV8.RoughWindow.not_forall_rough_coprime
#print axioms Erdos287.ResearchBankV8.RoughWindow.grid_glue_lcm
#print axioms Erdos287.ResearchBankV8.RoughWindow.onGrid_of_dvd
#print axioms Erdos287.ResearchBankV8.RoughWindow.lcm_mul_gcd
#print axioms Erdos287.ResearchBankV8.RoughWindow.lcm_not_product
#print axioms Erdos287.ResearchBankV8.RoughWindow.glue_example
#print axioms Erdos287.ResearchBankV8.RoughWindow.grid_point_common_iff
#print axioms Erdos287.ResearchBankV8.RoughWindow.common_grid_points_card
#print axioms Erdos287.ResearchBankV8.RoughWindow.fresh_prime_lcm
#print axioms Erdos287.ResearchBankV8.RoughWindow.fresh_prime_new_grid
#print axioms Erdos287.ResearchBankV8.RoughWindow.sharedGridOutput_of_inputs
#print axioms Erdos287.ResearchBankV8.Saturation.saturate_mono
#print axioms Erdos287.ResearchBankV8.Saturation.saturate_changed
#print axioms Erdos287.ResearchBankV8.Saturation.saturate_endpoint
#print axioms Erdos287.ResearchBankV8.Saturation.saturate_noAdjZero
#print axioms Erdos287.ResearchBankV8.Saturation.selected_subset_saturate
#print axioms Erdos287.ResearchBankV8.Saturation.saturate_forbidden_subset
#print axioms Erdos287.ResearchBankV8.Saturation.saturate_forbidden_eq
#print axioms Erdos287.ResearchBankV8.Saturation.saturate_new_dvd
#print axioms Erdos287.ResearchBankV8.Saturation.integral_of_dvd_sum
#print axioms Erdos287.ResearchBankV8.Saturation.saturate_denomEntry
#print axioms Erdos287.ResearchBankV8.Saturation.saturate_idem
#print axioms Erdos287.ResearchBankV8.Saturation.saturate_selects_divisors
#print axioms Erdos287.ResearchBankV8.Saturation.forbidden_saturate_subset_nonDivisors
#print axioms Erdos287.ResearchBankV8.Saturation.saturate_forbidden_small_of_interface
#print axioms Erdos287.ResearchBankV8.TernaryBlocker.pairwise_extendible
#print axioms Erdos287.ResearchBankV8.TernaryBlocker.ternary_incompatible
#print axioms Erdos287.ResearchBankV8.TernaryBlocker.ternary_incompatible_with_guard
#print axioms Erdos287.ResearchBankV8.TernaryBlocker.pairwise_compatibility_not_sufficient
#print axioms Erdos287.ResearchBankV8.VirtualEdge.virtual_edge_from_row
#print axioms Erdos287.ResearchBankV8.VirtualEdge.virtual_edge_nontrivial
#print axioms Erdos287.ResearchBankV8.VirtualEdge.virtual_edge_not_physical_contact
#print axioms Erdos287.ResearchBankV8.VirtualEdge.virtual_edges_not_independent
#print axioms Erdos287.ResearchBankV8.VirtualEdge.three_virtual_edges
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.dvd_lcmUpTo
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.lcmUpTo_ne_zero
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.prime_pow_dvd_finset_lcm
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.prime_pow_le_of_dvd_lcmUpTo
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.nondvd_lcmUpTo_isPrimePow
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.not_isPrimePow_of_coprime_mul
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_eq_true_iff
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.P_eq
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_two_dvd_M
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_three_dvd_M
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_T_eq
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_M_eq_two_T
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_T_odd
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_A_pos
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_A_le_T
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_T_ge_two
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_endpoints_selected
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_P_not_dvd
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_P_mem
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_even_zero_eq_P
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_P_sub_one_factor
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_P_sub_one_not_primePow
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_P_add_one_factor
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_P_add_one_not_primePow
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_noAdjZero
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.seed_denomEntry
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.weak_cutoff_entry_existence
#print axioms Erdos287.ResearchBankV8.WeakCutoffSeed.weak_cutoff_does_not_transfer
#print axioms Erdos287.ResearchBankV8.WholeParentCap.forced_card_le_sum
#print axioms Erdos287.ResearchBankV8.WholeParentCap.forced_card_eq_sum_of_disjoint
#print axioms Erdos287.ResearchBankV8.WholeParentCap.old_whole_parent_cap_incompatible
#print axioms Erdos287.ResearchBankV8.WholeParentCap.entry_alone_not_refuted
#print axioms Erdos287.ResearchBankV8.WholeParentCap.entryModel_cap_fails
