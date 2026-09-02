import RequestProject.Status.CurrentStatusErdos287SharedOtherFrontier

/-!
# Axiom audit — the 287A / shared-other45 frontier

This module is **append-only**.  It runs `#print axioms` on every principal new theorem of
the layer.  The expected output for each is the ordinary Mathlib set

```
[propext, Classical.choice, Quot.sound]
```

or a subset of it.  No custom axiom, no `sorryAx`, no `native_decide`, no `unsafe`, no
`opaque` and no `implemented_by` occurs anywhere in the new modules.
-/

namespace Erdos287
namespace SharedOtherFrontierAxiomAudit

/-! ## §1  The raw architecture -/

#print axioms Erdos287.SharedOtherRaw.rawPacket_is_a_two_lane_sum
#print axioms Erdos287.SharedOtherRaw.rawPacket_lanes_are_disjoint
#print axioms Erdos287.SharedOtherRaw.tot_constructor_excludes_forbidden_fields
#print axioms Erdos287.SharedOtherRaw.tot_datum_is_determined_by_its_listed_fields
#print axioms Erdos287.SharedOtherRaw.u_constructor_carries_the_listed_fields
#print axioms Erdos287.SharedOtherRaw.selectedE_congr
#print axioms Erdos287.SharedOtherRaw.EStar_is_deterministic
#print axioms Erdos287.SharedOtherRaw.A_eta_eq_zero_of_no_divisor
#print axioms Erdos287.SharedOtherRaw.B_eta_eq_zero_of_no_divisor
#print axioms Erdos287.SharedOtherRaw.generated_coefficients_depend_only_on_the_selected_E
#print axioms Erdos287.SharedOtherRaw.determinant_line_invariant
#print axioms Erdos287.SharedOtherRaw.determinant_line_forward
#print axioms Erdos287.SharedOtherRaw.determinant_line_converse
#print axioms Erdos287.SharedOtherRaw.census_determinant_line
#print axioms Erdos287.SharedOtherRaw.centred_two_copy_identity
#print axioms Erdos287.SharedOtherRaw.centred_two_copy_normSq
#print axioms Erdos287.SharedOtherRaw.coefficient_preservation
#print axioms Erdos287.SharedOtherRaw.coefficient_preservation_diagonal
#print axioms Erdos287.SharedOtherRaw.centred_two_copy_is_not_the_uncentred_square

#print axioms Erdos287.SharedOtherParent.selectedE_singleton
#print axioms Erdos287.SharedOtherParent.SharedConductorData.e_dvd_g₁
#print axioms Erdos287.SharedOtherParent.SharedConductorData.e_dvd_g₂
#print axioms Erdos287.SharedOtherParent.SharedConductorData.n₁_eq_div
#print axioms Erdos287.SharedOtherParent.SharedConductorData.n₂_eq_div
#print axioms Erdos287.SharedOtherParent.SharedConductorData.reduced_factors_coprime
#print axioms Erdos287.SharedOtherParent.SharedConductorData.q_factorisations
#print axioms Erdos287.SharedOtherParent.SharedConductorData.Delta_zero_iff_proportional
#print axioms Erdos287.SharedOtherParent.Delta_is_a_genuine_two_copy_object
#print axioms Erdos287.SharedOtherParent.deltaRoute_c0_iff
#print axioms Erdos287.SharedOtherParent.deltaRoute_transverse_iff
#print axioms Erdos287.SharedOtherParent.deltaRoute_bDiagonal_iff
#print axioms Erdos287.SharedOtherParent.deltaRoute_exists_unique
#print axioms Erdos287.SharedOtherParent.deltaRoute_is_routing_only
#print axioms Erdos287.SharedOtherParent.coefficientPattern_is_exactly_the_three_source_patterns
#print axioms Erdos287.SharedOtherParent.ford722_census_metadata
#print axioms Erdos287.SharedOtherParent.ford722_socket_is_a_genuine_constraint
#print axioms Erdos287.SharedOtherParent.ford722_socket_needs_k_at_least_one
#print axioms Erdos287.SharedOtherParent.betaG_profile_does_not_determine_the_generated_coefficients

#print axioms Erdos287.SharedOtherCompiler.raw_census_union
#print axioms Erdos287.SharedOtherCompiler.raw_census_disjoint
#print axioms Erdos287.SharedOtherCompiler.raw_census_card
#print axioms Erdos287.SharedOtherCompiler.tot_reconstruction_finite
#print axioms Erdos287.SharedOtherCompiler.totCensus_carries_no_U_datum
#print axioms Erdos287.SharedOtherCompiler.E_T_bound_of_typeI
#print axioms Erdos287.SharedOtherCompiler.littleO_is_a_genuine_constraint
#print axioms Erdos287.SharedOtherCompiler.E_L_bound_of_sharedOtherParent
#print axioms Erdos287.SharedOtherCompiler.sharedOtherParentInput_is_a_genuine_constraint
#print axioms Erdos287.SharedOtherCompiler.erdos287HardUAdapter_holds
#print axioms Erdos287.SharedOtherCompiler.adapters_are_independent
#print axioms Erdos287.SharedOtherCompiler.twin_adapter_is_not_inhabited_here
#print axioms Erdos287.SharedOtherCompiler.asymptoticFCL_of_shared_other_parent
#print axioms Erdos287.SharedOtherCompiler.asymptoticFCL_keeps_every_shared_source_input

/-! ## §2  The status layer of this frontier -/

#print axioms Erdos287.SharedOtherFrontierStatus.sharedOtherFrontier_is_later
#print axioms Erdos287.SharedOtherFrontierStatus.earlier_twoLane_ledger_retained_unchanged
#print axioms Erdos287.SharedOtherFrontierStatus.dependentRawPacket_row_is_kernel_proved
#print axioms Erdos287.SharedOtherFrontierStatus.generatedCoefficients_row_is_kernel_proved
#print axioms Erdos287.SharedOtherFrontierStatus.determinantLine_row_is_kernel_proved
#print axioms Erdos287.SharedOtherFrontierStatus.centredTwoCopy_row_is_kernel_proved
#print axioms Erdos287.SharedOtherFrontierStatus.deltaRouter_row_is_kernel_proved
#print axioms Erdos287.SharedOtherFrontierStatus.sharedConductorData_row_is_kernel_proved
#print axioms Erdos287.SharedOtherFrontierStatus.twoAdapters_row_is_kernel_proved
#print axioms Erdos287.SharedOtherFrontierStatus.E_L_row_is_conditional
#print axioms Erdos287.SharedOtherFrontierStatus.E_T_row_is_paper_closed_external
#print axioms Erdos287.SharedOtherFrontierStatus.hardU_row_is_open_external
#print axioms Erdos287.SharedOtherFrontierStatus.downstream_rows
#print axioms Erdos287.SharedOtherFrontierStatus.paperClosedExternal_is_not_kernelProved
#print axioms Erdos287.SharedOtherFrontierStatus.no_row_is_a_proof_claim
#print axioms Erdos287.SharedOtherFrontierStatus.first_open_research_socket_is_the_hard_U

end SharedOtherFrontierAxiomAudit
end Erdos287
