import Mathlib
import RequestProject.Status.Erdos287V24Status

/-!
# V24 axiom audit

`#print axioms` for every principal V24 declaration.  Only `propext`, `Classical.choice`
and `Quot.sound` may appear.  No external analytic theorem enters through a user axiom, and
no V24 file contains `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or
`@[implemented_by]`.
-/

-- V24Prefactor
#print axioms Erdos287.V24Prefactor.sp2CextRepaired_spec
#print axioms Erdos287.V24Prefactor.oldPrefactor_and_repaired_are_incompatible
#print axioms Erdos287.V24Prefactor.repairedPrefactor_not_automatic
#print axioms Erdos287.V24Prefactor.q35_netLogExponent_eq_neg_five_halves
#print axioms Erdos287.V24Prefactor.q35_netLogExponent_lt_neg_one
#print axioms Erdos287.V24Prefactor.q35_signed_log_margin
#print axioms Erdos287.V24Prefactor.q35_local_capacity_pass
#print axioms Erdos287.V24Prefactor.q35_capacity_is_not_balancedSeven

-- V24Source
#print axioms Erdos287.V24Source.HstarBalancedSeven_eq_depthSum
#print axioms Erdos287.V24Source.twoSign_reassembles_source_summand
#print axioms Erdos287.V24Source.P_sm_eq_sum_of_oneSign
#print axioms Erdos287.V24Source.oneSignPhysical_eq_comparison_summand
#print axioms Erdos287.V24Source.physicalTwoB_not_defined_from_principalQCell
#print axioms Erdos287.V24Source.principalQCell_carries_no_B
#print axioms Erdos287.V24Source.physicalSource_needs_external_twoB

-- V24Euler
#print axioms Erdos287.V24Euler.repairedLocalFactor_sub_one_bound
#print axioms Erdos287.V24Euler.repairedLocalFactor_eq_one_iff
#print axioms Erdos287.V24Euler.balancedSeven_at_most_seven_onP_factors
#print axioms Erdos287.V24Euler.balancedSeven_at_most_seven_oddPrimeDivisors
#print axioms Erdos287.V24Euler.euler_H0_eq_twoB
#print axioms Erdos287.V24Euler.eulerUniformity_reported_A0_pos
#print axioms Erdos287.V24Euler.eulerUniformity_not_automatic

-- V24FullQ
#print axioms Erdos287.V24FullQ.uCut_cube
#print axioms Erdos287.V24FullQ.balancedSeven_qr_threeWay_cover
#print axioms Erdos287.V24FullQ.balancedSeven_qr_threeWay_disjoint
#print axioms Erdos287.V24FullQ.sum_threeWay
#print axioms Erdos287.V24FullQ.sum_threeWay_sector
#print axioms Erdos287.V24FullQ.hardDyadic_partitionOfUnity
#print axioms Erdos287.V24FullQ.dyadic_supports_not_disjoint
#print axioms Erdos287.V24FullQ.hardPacketOwner_exists_unique
#print axioms Erdos287.V24FullQ.balancedSeven_fullQ_structural_partition
#print axioms Erdos287.V24FullQ.hardDyadicProvider_q35
#print axioms Erdos287.V24FullQ.hardDyadicProvider_not_all_owned
#print axioms Erdos287.V24FullQ.fullQ_ownership_incomplete

-- V24Adapters
#print axioms Erdos287.V24Adapters.sigma_threeWay_reassembly
#print axioms Erdos287.V24Adapters.sectorTargetNorm_nonneg
#print axioms Erdos287.V24Adapters.smallQ_closed_of_literal_typeI_adapter
#print axioms Erdos287.V24Adapters.smallQAdapter_not_automatic
#print axioms Erdos287.V24Adapters.smallR_closed_of_switched_typeI_adapter
#print axioms Erdos287.V24Adapters.smallRAdapter_not_automatic
#print axioms Erdos287.V24Adapters.smallQ_and_smallR_cells_differ
#print axioms Erdos287.V24Adapters.smallQ_smallR_both_open

-- V24Hard
#print axioms Erdos287.V24Hard.q35Cext_eq_one
#print axioms Erdos287.V24Hard.q35_Q_mul_R_eq_X
#print axioms Erdos287.V24Hard.q35_smoothCut_lt_Q
#print axioms Erdos287.V24Hard.q35_inside_hard_sector
#print axioms Erdos287.V24Hard.hardDyadic_owner_only_q35
#print axioms Erdos287.V24Hard.q35_packet
#print axioms Erdos287.V24Hard.hardDyadic_census_incomplete
#print axioms Erdos287.V24Hard.hardDyadicExhaustiveness_not_automatic
#print axioms Erdos287.V24Hard.hardCell_twoSign_total
#print axioms Erdos287.V24Hard.hardCell_oneSign_insufficient
#print axioms Erdos287.V24Hard.q35_closure_is_not_balancedSeven

-- V24FullQCompiler
#print axioms Erdos287.V24FullQCompiler.allQProviderExhaustive_of_inputs
#print axioms Erdos287.V24FullQCompiler.sp2BalancedSevenFullQ_of_inputs
#print axioms Erdos287.V24FullQCompiler.balancedSevenAsymptotic_of_fullQ_and_comparison
#print axioms Erdos287.V24FullQCompiler.allQProviderInputs_currently_unavailable
#print axioms Erdos287.V24FullQCompiler.fullQ_status_stays_open
#print axioms Erdos287.V24FullQCompiler.fullQ_bound_gives_no_threshold

-- V24Status
#print axioms Erdos287.V24Status.v24_prefactor_repaired
#print axioms Erdos287.V24Status.v24_q35_local_numerology
#print axioms Erdos287.V24Status.v24_finite_layer_proved
#print axioms Erdos287.V24Status.v24_external_layer_uninhabited
#print axioms Erdos287.V24Status.v24_provider_exhaustiveness_fails
#print axioms Erdos287.V24Status.v24_q35_is_one_cell_only
#print axioms Erdos287.V24Status.v24_first_exact_residual
#print axioms Erdos287.V24Status.v24_census_not_activated
#print axioms Erdos287.V24Status.v24_effectivity_separate
#print axioms Erdos287.V24Status.v24_fullQ_and_erdos287_open
