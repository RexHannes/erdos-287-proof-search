import RequestProject.Erdos287.SourceChain.FCHSPropagation
import RequestProject.Erdos287.SourceChain.V100Kernel71
import RequestProject.Erdos287.SourceChain.Physical.TypeII.ScopedProviders
import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremCounterexample
import RequestProject.Erdos287.SourceChain.Physical.TypeII.RepairedProviders
import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyActual
import RequestProject.Erdos287.SourceChain.Physical.TypeII.UremFamilyFinal

/-! Axiom audit for the FCHS propagation lemmas and the parameter / provider-scope repair. -/

open Erdos287.SourceChain Erdos287.Physical.TypeII

#print axioms FCHS_le_B0CS2
#print axioms FCHS_le_const_B0CS2
#print axioms pascadiInner_le_two
#print axioms pascadiInner_le_const
#print axioms sqrt_pascadiInner_le
#print axioms pascadi_g_scaling
#print axioms pascadi_g_scaling_le
#print axioms pascadi_normalized_identity
#print axioms regr_normalizations_differ
#print axioms old_packet_margin_neg
#print axioms new_packet_margin_eq
#print axioms new_packet_margin_pos
#print axioms sigmaBase_le_eps_div_100
#print axioms two_deltaSpec_lt_sigma
#print axioms SWSeq_of_masked
#print axioms pascadi_scoped_of_old
#print axioms bvUrem_scoped_of_old
#print axioms scalarTypeII_bound_of_scopedProviders

/-! Refutation of the scoped remainder provider (`UremCounterexample.lean`). -/
#print axioms ellX_three
#print axioms physUrem_eq_three
#print axioms two_pow_le_primes
#print axioms exists_prime_block
#print axioms inner_sum_eq
#print axioms not_ordinaryBVUremProviderScoped
#print axioms not_ordinaryBVUremProvider
#print axioms scopedProviders_inconsistent
#print axioms PhysData.prime_dvd_f_of_dvd_AB

/-! Repaired (still unproved) provider statements (`RepairedProviders.lean`). -/
#print axioms uremCE_data_not_admissible
#print axioms physData_affinePrimesDivideBase
#print axioms pascadi_repaired_of_scoped
#print axioms bvUrem_repaired_of_scoped
#print axioms scalarTypeII_bound_of_repairedProviders

/-! Family-averaged Urem repair (`UremFamily*.lean`): finite adapter, composition, Maynard input. -/
#print axioms UremFamily.relDisc_eq_projection
#print axioms UremFamily.relDisc_energy_le
#print axioms UremFamily.count_Ico_modEq_le
#print axioms UremFamily.packet_weighted_cauchy
#print axioms UremFamily.inner_urem_eq_relDisc
#print axioms UremFamily.sum_occupancy_le
#print axioms UremFamily.urem_r_sq_le_relative_energy
#print axioms UremFamily.packet_bound
#print axioms UremFamily.energy_grouping
#print axioms UremFamily.family_urem_le_bdhEnergy
#print axioms UremFamily.physUrem_eq_uremBlocks
#print axioms UremFamily.physical_family_urem_le
#print axioms UremFamily.swCondition_masked
#print axioms UremFamily.bdhEnergy_masked_le
#print axioms UremFamily.physical_family_urem_maynard
#print axioms UremFamily.packet_multiplicity
#print axioms UremFamily.actual_family_urem_maynard
#print axioms UremFamily.group_typeII_sub_cells_le

/-! Urem branch completion (`UremFamilyMoments/SW/Aggregate/Cell/Final.lean`). -/
#print axioms UremFamily.sum_tau_pow_div_le
#print axioms UremFamily.nat_le_card_divisors_mul_totient
#print axioms UremFamily.sum_tau_pow_div_totient_le
#print axioms UremFamily.sum_tau_pow_le
#print axioms UremFamily.swCondition_of_intervalSW
#print axioms UremFamily.intervalSW_trunc
#print axioms UremFamily.abel_bound
#print axioms UremFamily.swCondition_log_of_intervalSW
#print axioms UremFamily.alphaSeq_swCondition
#print axioms UremFamily.alphaSeq_abs_le_tau
#print axioms UremFamily.packet_density_le
#print axioms UremFamily.atom_total_le
#print axioms UremFamily.actual_family_urem_explicit
#print axioms UremFamily.physUrem_scale_left
#print axioms UremFamily.physUrem_sum_right
#print axioms UremFamily.betaSeq_lt
#print axioms UremFamily.betaSeq_eq_sum_dy
#print axioms UremFamily.betaSeq_dy_sq_le
#print axioms UremFamily.cell_urem_bound
#print axioms UremFamily.pieces_sum_le
#print axioms UremFamily.cell_urem_polylog
#print axioms UremFamily.card_cellBox
#print axioms UremFamily.cells_urem_polylog

-- V100R4S §6 ratio ledger and conditional (6.8)-shape W₄ bound
#print axioms Erdos287.SourceChain.diag_ratio
#print axioms Erdos287.SourceChain.ram_ratio
#print axioms Erdos287.SourceChain.ratio_6_6a
#print axioms Erdos287.SourceChain.ratio_6_6b
#print axioms Erdos287.SourceChain.ratio_6_6c
#print axioms Erdos287.SourceChain.ratio_6_6d
#print axioms Erdos287.SourceChain.H0_div_S_ratio
#print axioms Erdos287.SourceChain.bracket_H_le
#print axioms Erdos287.SourceChain.spec_source_bound
#print axioms Erdos287.SourceChain.diag_source_bound
#print axioms Erdos287.SourceChain.ram_source_bound
#print axioms Erdos287.SourceChain.W4_uniform_bound
#print axioms Erdos287.SourceChain.W4_uniform_bound_6eps
#print axioms Erdos287.SourceChain.kernel_7_1
#print axioms Erdos287.SourceChain.kernel_1_8
#print axioms Erdos287.SourceChain.kernel_1_9
#print axioms Erdos287.SourceChain.kernel_1_9_of_narrow
