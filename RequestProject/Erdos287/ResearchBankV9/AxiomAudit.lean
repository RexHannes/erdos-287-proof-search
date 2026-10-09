import RequestProject.Erdos287.ResearchBankV9.AffineContact
import RequestProject.Erdos287.ResearchBankV9.ArchitectureLimit
import RequestProject.Erdos287.ResearchBankV9.AsraCRT
import RequestProject.Erdos287.ResearchBankV9.AsraClearing
import RequestProject.Erdos287.ResearchBankV9.AsraInterfaces
import RequestProject.Erdos287.ResearchBankV9.AsraPrimeSlot
import RequestProject.Erdos287.ResearchBankV9.AsraZeroMode
import RequestProject.Erdos287.ResearchBankV9.CircularGraph
import RequestProject.Erdos287.ResearchBankV9.Gates
import RequestProject.Erdos287.ResearchBankV9.GcdClique
import RequestProject.Erdos287.ResearchBankV9.GraphLocalization
import RequestProject.Erdos287.ResearchBankV9.Ledger
import RequestProject.Erdos287.ResearchBankV9.Occupancy
import RequestProject.Erdos287.ResearchBankV9.Splice

/-!
# Research Bank V9 — axiom audit

`#print axioms` for every theorem of the V9 layer.  Expected output: only `propext`,
`Classical.choice`, `Quot.sound` (or no axioms at all).  No `sorryAx`, no native-evaluation
axiom, no custom research axiom.
-/

#print axioms Erdos287.ResearchBankV9.AffineContact.cofactors
#print axioms Erdos287.ResearchBankV9.AffineContact.affine_contact_identity
#print axioms Erdos287.ResearchBankV9.AffineContact.contact_locations
#print axioms Erdos287.ResearchBankV9.AffineContact.contact_in_window_iff
#print axioms Erdos287.ResearchBankV9.AffineContact.contact_example
#print axioms Erdos287.ResearchBankV9.ArchitectureLimit.periodic_indep
#print axioms Erdos287.ResearchBankV9.ArchitectureLimit.periodic_cover
#print axioms Erdos287.ResearchBankV9.ArchitectureLimit.architecture_upper_limit
#print axioms Erdos287.ResearchBankV9.ArchitectureLimit.limit_eq_rho_add_one
#print axioms Erdos287.ResearchBankV9.ArchitectureLimit.gate_is_limit_at_rho
#print axioms Erdos287.ResearchBankV9.AsraCRT.root_iff_slot
#print axioms Erdos287.ResearchBankV9.AsraCRT.slot_unique
#print axioms Erdos287.ResearchBankV9.AsraCRT.dvd_Dmod_iff
#print axioms Erdos287.ResearchBankV9.AsraCRT.Dmod_pos
#print axioms Erdos287.ResearchBankV9.AsraCRT.exists_root_mod
#print axioms Erdos287.ResearchBankV9.AsraCRT.crt_root_bijection
#print axioms Erdos287.ResearchBankV9.AsraCRT.roots_distinguish_allocations
#print axioms Erdos287.ResearchBankV9.AsraCRT.collision_zero
#print axioms Erdos287.ResearchBankV9.AsraCRT.spectator_collision_zero
#print axioms Erdos287.ResearchBankV9.AsraCRT.joint_modulus_iff
#print axioms Erdos287.ResearchBankV9.AsraCRT.lcm_ne_product_fixture
#print axioms Erdos287.ResearchBankV9.AsraCRT.clean_main_modulus
#print axioms Erdos287.ResearchBankV9.AsraClearing.clearing_iff
#print axioms Erdos287.ResearchBankV9.AsraClearing.alphaT_support
#print axioms Erdos287.ResearchBankV9.AsraClearing.alphaT_mul
#print axioms Erdos287.ResearchBankV9.AsraClearing.alphaT_divisor_bound
#print axioms Erdos287.ResearchBankV9.AsraClearing.base_progression_iff
#print axioms Erdos287.ResearchBankV9.AsraClearing.fixed_denominator_does_not_delete_base
#print axioms Erdos287.ResearchBankV9.AsraInterfaces.asra_of_components
#print axioms Erdos287.ResearchBankV9.AsraInterfaces.pairCoefficient_below_gate_of_asra
#print axioms Erdos287.ResearchBankV9.AsraInterfaces.nonzeroFrequencyTransfer_not_automatic
#print axioms Erdos287.ResearchBankV9.AsraInterfaces.signedSieveMainTerm_not_automatic
#print axioms Erdos287.ResearchBankV9.AsraInterfaces.asra_not_automatic
#print axioms Erdos287.ResearchBankV9.AsraPrimeSlot.primeSlot_truncation
#print axioms Erdos287.ResearchBankV9.AsraPrimeSlot.primeSlot_truncation_sq
#print axioms Erdos287.ResearchBankV9.AsraPrimeSlot.upper_sieve_majorization
#print axioms Erdos287.ResearchBankV9.AsraPrimeSlot.primePair_bound_of_upperSieve
#print axioms Erdos287.ResearchBankV9.AsraPrimeSlot.dvd_sum_eq_root_classes
#print axioms Erdos287.ResearchBankV9.AsraPrimeSlot.largeOverlap_tail_bound
#print axioms Erdos287.ResearchBankV9.AsraZeroMode.lcm_dvd_int
#print axioms Erdos287.ResearchBankV9.AsraZeroMode.sol_unique
#print axioms Erdos287.ResearchBankV9.AsraZeroMode.compat_of_sol
#print axioms Erdos287.ResearchBankV9.AsraZeroMode.sol_exists
#print axioms Erdos287.ResearchBankV9.AsraZeroMode.zeroMode_card
#print axioms Erdos287.ResearchBankV9.AsraZeroMode.zeroMode_density
#print axioms Erdos287.ResearchBankV9.AsraZeroMode.compat_iff_ratio
#print axioms Erdos287.ResearchBankV9.AsraZeroMode.centred_kernel_eq
#print axioms Erdos287.ResearchBankV9.AsraZeroMode.ratio_indicator_average
#print axioms Erdos287.ResearchBankV9.AsraZeroMode.centred_kernel_sum_zero
#print axioms Erdos287.ResearchBankV9.AsraZeroMode.smallOverlap_zeroFrequency_bound
#print axioms Erdos287.ResearchBankV9.CircularGraph.emod_eq_of_dvd_sub
#print axioms Erdos287.ResearchBankV9.CircularGraph.near_iff
#print axioms Erdos287.ResearchBankV9.CircularGraph.card_le_of_diam
#print axioms Erdos287.ResearchBankV9.CircularGraph.indep_card_le
#print axioms Erdos287.ResearchBankV9.CircularGraph.arc_indep
#print axioms Erdos287.ResearchBankV9.CircularGraph.count_shift_lt
#print axioms Erdos287.ResearchBankV9.CircularGraph.sum_swap
#print axioms Erdos287.ResearchBankV9.CircularGraph.fracColouring_value_ge
#print axioms Erdos287.ResearchBankV9.CircularGraph.arc_indep'
#print axioms Erdos287.ResearchBankV9.CircularGraph.arcColouring_value
#print axioms Erdos287.ResearchBankV9.CircularGraph.fractional_chromatic_eq
#print axioms Erdos287.ResearchBankV9.Gates.alphaEq_of
#print axioms Erdos287.ResearchBankV9.Gates.gate_13_3
#print axioms Erdos287.ResearchBankV9.Gates.gate_145_38
#print axioms Erdos287.ResearchBankV9.Gates.gate_ineq
#print axioms Erdos287.ResearchBankV9.Gates.gate_margin
#print axioms Erdos287.ResearchBankV9.Gates.gate_iff
#print axioms Erdos287.ResearchBankV9.Gates.gate_eq_rho_add_one
#print axioms Erdos287.ResearchBankV9.Gates.localization_constant
#print axioms Erdos287.ResearchBankV9.Gates.gate_near_architecture_limit
#print axioms Erdos287.ResearchBankV9.GcdClique.gcd_eq_diff_iff
#print axioms Erdos287.ResearchBankV9.GcdClique.clique_translate_iff
#print axioms Erdos287.ResearchBankV9.GcdClique.gcd_lcm_dvd_lcm_gcd
#print axioms Erdos287.ResearchBankV9.GcdClique.lcmList_ne_zero
#print axioms Erdos287.ResearchBankV9.GcdClique.dvd_lcmList
#print axioms Erdos287.ResearchBankV9.GcdClique.gcd_lcmList_dvd
#print axioms Erdos287.ResearchBankV9.GcdClique.two_crt
#print axioms Erdos287.ResearchBankV9.GcdClique.crt_exists
#print axioms Erdos287.ResearchBankV9.GcdClique.compatible_of_solution
#print axioms Erdos287.ResearchBankV9.GcdClique.crt_exists_ge
#print axioms Erdos287.ResearchBankV9.GcdClique.mem_pairs
#print axioms Erdos287.ResearchBankV9.GcdClique.cliqueSystem_ne_zero
#print axioms Erdos287.ResearchBankV9.GcdClique.gcdClique_of_compatible
#print axioms Erdos287.ResearchBankV9.GcdClique.compatible_of_clique
#print axioms Erdos287.ResearchBankV9.GcdClique.clique_0124
#print axioms Erdos287.ResearchBankV9.GcdClique.shape_matters
#print axioms Erdos287.ResearchBankV9.GraphLocalization.contact_above_N
#print axioms Erdos287.ResearchBankV9.GraphLocalization.contact_contradiction
#print axioms Erdos287.ResearchBankV9.GraphLocalization.Rigid.excluded
#print axioms Erdos287.ResearchBankV9.GraphLocalization.no_gap2CE_of_usefulEdge
#print axioms Erdos287.ResearchBankV9.GraphLocalization.no_erdos287Counterexample_of_usefulEdge
#print axioms Erdos287.ResearchBankV9.GraphLocalization.no_counterexample_above_of_edge_supply
#print axioms Erdos287.ResearchBankV9.Ledger.v9New_no_closed
#print axioms Erdos287.ResearchBankV9.Ledger.v9_no_closed
#print axioms Erdos287.ResearchBankV9.Ledger.v9_erdos287_open
#print axioms Erdos287.ResearchBankV9.Ledger.v9_record_external_not_proved
#print axioms Erdos287.ResearchBankV9.Ledger.v9_proved_implies_kernel
#print axioms Erdos287.ResearchBankV9.Ledger.asra_epochs
#print axioms Erdos287.ResearchBankV9.Ledger.splice_blocked
#print axioms Erdos287.ResearchBankV9.Ledger.step_provedNodes
#print axioms Erdos287.ResearchBankV9.Ledger.derivable_eq
#print axioms Erdos287.ResearchBankV9.Ledger.no_ledger_path_closes_erdos287
#print axioms Erdos287.ResearchBankV9.Ledger.every_edge_has_open_premise
#print axioms Erdos287.ResearchBankV9.Occupancy.occupancy_forces_edge
#print axioms Erdos287.ResearchBankV9.Occupancy.occupancy_programme
#print axioms Erdos287.ResearchBankV9.Occupancy.circular_occupancy
#print axioms Erdos287.ResearchBankV9.Splice.splice
#print axioms Erdos287.ResearchBankV9.Splice.eventual_exclusion_conditional
#print axioms Erdos287.ResearchBankV9.Splice.current_M0_unavailable
#print axioms Erdos287.ResearchBankV9.Splice.M0_ge
#print axioms Erdos287.ResearchBankV9.Splice.effectiveSplice_iff_no_counterexample
#print axioms Erdos287.ResearchBankV9.Splice.asymptotic_without_threshold_does_not_splice
#print axioms Erdos287.ResearchBankV9.Splice.finite_obstruction_not_asymptotic
#print axioms Erdos287.ResearchBankV9.Splice.conditional_does_not_inhabit_premise
