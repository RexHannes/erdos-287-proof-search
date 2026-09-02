import RequestProject.Status.CurrentStatusErdos287TwoLaneFCLFrontier

/-!
# Axiom audit — the two-lane FCL frontier

This module is **append-only**.  It runs `#print axioms` on every principal new theorem of
the layer.  The expected output for each is the ordinary Mathlib set

```
[propext, Classical.choice, Quot.sound]
```

or a subset of it (the purely decidable rows depend on no axioms at all).  No custom axiom,
no `sorryAx`, no `native_decide`, no `unsafe`, no `opaque` and no `implemented_by` occurs
anywhere in the new modules.
-/

namespace Erdos287
namespace TwoLaneFCLFrontierAxiomAudit

/-! ## §1  The two-lane raw source -/

#print axioms Erdos287.TwoLaneRawSource.tot_carries_no_selectedE
#print axioms Erdos287.TwoLaneRawSource.raw_source_two_lane_union
#print axioms Erdos287.TwoLaneRawSource.raw_source_two_lane_disjoint
#print axioms Erdos287.TwoLaneRawSource.raw_source_two_lane_card
#print axioms Erdos287.TwoLaneRawSource.raw_source_two_lane_sum
#print axioms Erdos287.TwoLaneRawSource.u_lane_owns_the_selectedE_data
#print axioms Erdos287.TwoLaneRawSource.selectedE_mem
#print axioms Erdos287.TwoLaneRawSource.selectedE_min
#print axioms Erdos287.TwoLaneRawSource.selectedE_unique_per_row
#print axioms Erdos287.TwoLaneRawSource.selectedE_is_canonical_when_ranks_separate
#print axioms Erdos287.TwoLaneRawSource.independent_selection_duplicates_a_row
#print axioms Erdos287.TwoLaneRawSource.inclusionExclusionSign_odd
#print axioms Erdos287.TwoLaneRawSource.inclusionExclusionSign_even
#print axioms Erdos287.TwoLaneRawSource.packetId_is_discrete
#print axioms Erdos287.TwoLaneRawSource.census_is_ordinate_free
#print axioms Erdos287.TwoLaneRawSource.ordinate_in_the_id_breaks_the_census
#print axioms Erdos287.TwoLaneRawSource.routeRepeated_correct
#print axioms Erdos287.TwoLaneRawSource.routeRepeated_exhaustive
#print axioms Erdos287.TwoLaneRawSource.distinct_branch_subset_expansion_is_literal
#print axioms Erdos287.TwoLaneRawSource.repeated_row_would_be_overcounted
#print axioms Erdos287.TwoLaneRawSource.repeated_copies_are_one_divisor
#print axioms Erdos287.TwoLaneRawSource.exponent_representation_separates_the_branches

#print axioms Erdos287.OneCopyTwoCopy.owner1_card
#print axioms Erdos287.OneCopyTwoCopy.owner1_embedding_injective
#print axioms Erdos287.OneCopyTwoCopy.owner1_excludes_two_copy_owners
#print axioms Erdos287.OneCopyTwoCopy.delta_is_not_a_one_copy_coordinate
#print axioms Erdos287.OneCopyTwoCopy.omega_partition_reused
#print axioms Erdos287.OneCopyTwoCopy.omega_elementary_norm
#print axioms Erdos287.OneCopyTwoCopy.sharedGcd_is_not_a_one_copy_object
#print axioms Erdos287.OneCopyTwoCopy.owner2_card
#print axioms Erdos287.OneCopyTwoCopy.owner2_c0_iff
#print axioms Erdos287.OneCopyTwoCopy.owner2_transverse_iff
#print axioms Erdos287.OneCopyTwoCopy.owner2_bDiagonal_iff
#print axioms Erdos287.OneCopyTwoCopy.owner2_exists_unique
#print axioms Erdos287.OneCopyTwoCopy.owner2_is_not_a_one_copy_assignment
#print axioms Erdos287.OneCopyTwoCopy.owner_levels_are_disjoint

#print axioms Erdos287.HeathBrownSource.sourceConsistency_is_a_real_constraint
#print axioms Erdos287.HeathBrownSource.sourceConsistent_determines_the_moebius_fields
#print axioms Erdos287.HeathBrownSource.exact_coefficient_need_not_be_one_bounded
#print axioms Erdos287.HeathBrownSource.majorant_is_not_the_source_coefficient

#print axioms Erdos287.N2Finite.omega_le_six
#print axioms Erdos287.N2Finite.omega_le_six_sharp
#print axioms Erdos287.N2Finite.subvector_expansion_bound
#print axioms Erdos287.N2Finite.squarefree_split
#print axioms Erdos287.N2Finite.shifted_prime_split
#print axioms Erdos287.N2Finite.proper_prime_power_characterisation
#print axioms Erdos287.N2Finite.rootCount_of_dvd
#print axioms Erdos287.N2Finite.rootCount_of_not_dvd
#print axioms Erdos287.N2Finite.nu_two
#print axioms Erdos287.N2Finite.nu_odd_dvd
#print axioms Erdos287.N2Finite.nu_odd_not_dvd
#print axioms Erdos287.N2Finite.singularSeries_input_is_a_genuine_constraint

#print axioms Erdos287.TwoLaneMaster.twoLane_socket_is_a_genuine_constraint
#print axioms Erdos287.TwoLaneMaster.twoLane_socket_has_no_one_copy_two_copy_owner
#print axioms Erdos287.TwoLaneMaster.E_L_channel_of_twoLane
#print axioms Erdos287.TwoLaneMaster.E_T_channel_of_twoLane
#print axioms Erdos287.TwoLaneMaster.fixed_eps_collar_is_not_vanishing
#print axioms Erdos287.TwoLaneMaster.n2_paper_input_is_a_genuine_constraint
#print axioms Erdos287.TwoLaneMaster.bsrc_paper_input_is_a_genuine_constraint
#print axioms Erdos287.TwoLaneMaster.asymptoticFCL_of_paper_inputs
#print axioms Erdos287.TwoLaneMaster.asymptoticFCL_keeps_every_external_input
#print axioms Erdos287.TwoLaneMaster.erdos287Statement_of_explicit_research_inputs
#print axioms Erdos287.TwoLaneMaster.explicit_thresholds_not_supplied

/-! ## §2  The status layer of this frontier -/

#print axioms Erdos287.TwoLaneFCLFrontierStatus.twoLaneFCLFrontier_is_later
#print axioms Erdos287.TwoLaneFCLFrontierStatus.earlier_endgame_ledger_retained_unchanged
#print axioms Erdos287.TwoLaneFCLFrontierStatus.twoLaneRawSource_row_is_kernel_proved
#print axioms Erdos287.TwoLaneFCLFrontierStatus.selectedE_row_is_kernel_proved
#print axioms Erdos287.TwoLaneFCLFrontierStatus.repeatedPrime_row_is_kernel_proved
#print axioms Erdos287.TwoLaneFCLFrontierStatus.heathBrown_row_is_kernel_proved
#print axioms Erdos287.TwoLaneFCLFrontierStatus.ownerLevel_row_is_kernel_proved
#print axioms Erdos287.TwoLaneFCLFrontierStatus.n2Finite_row_is_kernel_proved
#print axioms Erdos287.TwoLaneFCLFrontierStatus.asymptoticFCL_row_is_conditional
#print axioms Erdos287.TwoLaneFCLFrontierStatus.fclToWindowPair_row_is_conditional
#print axioms Erdos287.TwoLaneFCLFrontierStatus.bridge_threshold_row_is_twelve
#print axioms Erdos287.TwoLaneFCLFrontierStatus.endToEnd_row_is_conditional
#print axioms Erdos287.TwoLaneFCLFrontierStatus.open_rows
#print axioms Erdos287.TwoLaneFCLFrontierStatus.paperClosedExternal_is_not_kernelProved
#print axioms Erdos287.TwoLaneFCLFrontierStatus.superseded_is_not_a_deletion
#print axioms Erdos287.TwoLaneFCLFrontierStatus.first_open_research_socket_is_the_master_compiler_v2
#print axioms Erdos287.TwoLaneFCLFrontierStatus.no_row_is_a_proof_claim

end TwoLaneFCLFrontierAxiomAudit
end Erdos287
