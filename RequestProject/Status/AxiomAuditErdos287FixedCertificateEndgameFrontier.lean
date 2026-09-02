import RequestProject.Status.CurrentStatusErdos287FixedCertificateEndgameFrontier

/-!
# Axiom audit — the fixed-certificate endgame frontier

This module is **append-only**.  It runs `#print axioms` on every principal new theorem of
the layer.  The expected output for each is the ordinary Mathlib set

```
[propext, Classical.choice, Quot.sound]
```

or a subset of it (several purely decidable rows depend on no axioms at all).  No custom
axiom, no `sorryAx`, no `native_decide`, no `unsafe`, no `opaque` and no `implemented_by`
occurs anywhere in the new modules.
-/

namespace Erdos287
namespace FixedCertificateEndgameAxiomAudit

/-! ## §1  The repaired fixed-certificate data -/

#print axioms Erdos287.FixedCertificateRepair.repairedC2_eq_one
#print axioms Erdos287.FixedCertificateRepair.repairedC2_is_a_choice
#print axioms Erdos287.FixedCertificateRepair.gPerturb_eq_on_core
#print axioms Erdos287.FixedCertificateRepair.gPerturb_eq_zero_outside
#print axioms Erdos287.FixedCertificateRepair.gPerturb_zero_eps
#print axioms Erdos287.FixedCertificateRepair.gPerturb_window_antitone
#print axioms Erdos287.FixedCertificateRepair.gPerturb_is_not_a_scalar_shrink
#print axioms Erdos287.FixedCertificateRepair.gPerturb_agrees_with_scalar_shrink_only_trivially

/-! ## §2  The physical support partition and the physical weights -/

#print axioms Erdos287.PhysicalSupport.PhysicalSupportData.support_partition_union
#print axioms Erdos287.PhysicalSupport.PhysicalSupportData.regions_disjoint
#print axioms Erdos287.PhysicalSupport.PhysicalSupportData.support_partition_disjoint
#print axioms Erdos287.PhysicalSupport.PhysicalSupportData.support_partition_card
#print axioms Erdos287.PhysicalSupport.PhysicalSupportData.sum_partition
#print axioms Erdos287.PhysicalSupport.PhysicalSupportData.NX_partition
#print axioms Erdos287.PhysicalSupport.PhysicalWeightData.wX_def
#print axioms Erdos287.PhysicalSupport.PhysicalWeightData.aX_eq_bX_add_wX
#print axioms Erdos287.PhysicalSupport.PhysicalWeightData.weights_vanish_off_window
#print axioms Erdos287.PhysicalSupport.PhysicalWeightData.bX_determines_Bsrc
#print axioms Erdos287.PhysicalSupport.PhysicalWeightData.bsrcPin_not_automatic
#print axioms Erdos287.PhysicalSupport.channels_decompose_totalCorr
#print axioms Erdos287.PhysicalSupport.P_correlation_eq_mass_difference

/-! ## §3  The four-error transference algebra -/

#print axioms Erdos287.FourErrorTransference.FourChannelBudget.totalError_identity
#print axioms Erdos287.FourErrorTransference.fourRegion_transference
#print axioms Erdos287.FourErrorTransference.primeMass_pos_of_channel_budget
#print axioms Erdos287.FourErrorTransference.transference_has_no_factor_three
#print axioms Erdos287.FourErrorTransference.channel_budget_is_an_input
#print axioms Erdos287.FourErrorTransference.publishedLimitingMargin_pos
#print axioms Erdos287.FourErrorTransference.smallEps_margin_gives_no_explicit_eps0
#print axioms Erdos287.FourErrorTransference.positiveMarginSupply_still_uninhabited
#print axioms Erdos287.FourErrorTransference.transference_with_supplied_margin

/-! ## §4  The endgame research sockets -/

#print axioms Erdos287.EndgameSockets.owner_is_exactly_six
#print axioms Erdos287.EndgameSockets.fordSourceIndex_carries_owner
#print axioms Erdos287.EndgameSockets.masterSource_socket_is_a_genuine_constraint
#print axioms Erdos287.EndgameSockets.masterSource_socket_not_inhabited_here
#print axioms Erdos287.EndgameSockets.vanishing_gives_collar_at_each_scale
#print axioms Erdos287.EndgameSockets.boundedSequence_excludes_lambda_growth
#print axioms Erdos287.EndgameSockets.boundedSequence_does_not_give_the_collar
#print axioms Erdos287.EndgameSockets.n2Collar_socket_is_a_genuine_constraint
#print axioms Erdos287.EndgameSockets.bsrcComparison_socket_is_a_genuine_constraint
#print axioms Erdos287.EndgameSockets.bsrc_is_not_replaced_by_an_arbitrary_B
#print axioms Erdos287.EndgameSockets.ford83_constants_give_positive_margin_below_threshold
#print axioms Erdos287.EndgameSockets.ford83_constants_socket_uninhabited_here

/-! ## §5  The conditional FCL compiler -/

#print axioms Erdos287.EndgameFCL.totalCorr_eq_fullCorrelation
#print axioms Erdos287.EndgameFCL.E_T_bound_of_masterSource_and_analyticKernel
#print axioms Erdos287.EndgameFCL.E_L_bound_of_uSourceSubset
#print axioms Erdos287.EndgameFCL.leakage_not_implied_by_total
#print axioms Erdos287.EndgameFCL.fixedCertificatePositiveMass_of_all_sockets
#print axioms Erdos287.EndgameFCL.fcl_compiler_keeps_every_analytic_hypothesis
#print axioms Erdos287.EndgameFCL.fixedCertificatePositiveMass_not_established

/-! ## §6  The threshold-`12` bridge -/

#print axioms Erdos287.FCLWindowPair.windowPairSupply_of_positiveFCLMass_twelve
#print axioms Erdos287.FCLWindowPair.windowPairSupply_twelve
#print axioms Erdos287.FCLWindowPair.bridge_threshold_is_twelve
#print axioms Erdos287.FCLWindowPair.threshold_twelve_subsumes_threshold_twenty
#print axioms Erdos287.FCLWindowPair.bridge_needs_the_support_condition

/-! ## §7  Effectivity and the end-to-end conditional compiler -/

#print axioms Erdos287.EndgameEffectivity.asymptoticFCL_of_effectiveFCL
#print axioms Erdos287.EndgameEffectivity.asymptoticFCL_does_not_give_bounded_effective
#print axioms Erdos287.EndgameEffectivity.effectiveWindowPairSupply_bounded
#print axioms Erdos287.EndgameEffectivity.effectivity_socket_is_a_genuine_constraint
#print axioms Erdos287.EndgameEffectivity.erdos287Statement_of_effectivityInput
#print axioms Erdos287.EndgameEffectivity.erdos287_remains_open

/-! ## §8  The status layer -/

#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.fixedCertificateEndgameFrontier_is_later
#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.earlier_layers_retained_unchanged
#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.supportPartition_row_is_kernel_proved
#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.fourErrorAlgebra_row_is_kernel_proved
#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.repairedCertificate_row_is_kernel_proved
#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.fclToWindowPairTwelve_row_is_kernel_proved_conditional
#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.master_source_row_is_open
#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.n2_collar_row_is_open
#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.bsrc_comparison_row_is_open
#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.positive_margin_row_is_open
#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.ford83_constants_row_is_open
#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.effectivity_row_is_open
#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.downstream_rows_open
#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.first_open_research_socket_is_the_master_source
#print axioms Erdos287.FixedCertificateEndgameFrontierStatus.no_row_is_a_proof_claim

end FixedCertificateEndgameAxiomAudit
end Erdos287
