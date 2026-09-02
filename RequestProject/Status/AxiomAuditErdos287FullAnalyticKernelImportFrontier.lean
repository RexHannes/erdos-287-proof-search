import RequestProject.Status.CurrentStatusErdos287FullAnalyticKernelImportFrontier

/-!
# Axiom audit — full analytic-kernel import frontier

This module is **append-only**.  It runs `#print axioms` on every principal new
theorem of the layer.  The expected output for each is the ordinary Mathlib set

```
[propext, Classical.choice, Quot.sound]
```

or a subset of it (several purely decidable rows depend on no axioms at all).
No custom axiom, no `sorryAx`, no `native_decide`, no `unsafe`, no `opaque` and
no `implemented_by` occurs anywhere in the new modules.
-/

namespace Erdos287
namespace FullAnalyticKernelImportAxiomAudit

/-! ## §1  The external analytic input -/

#print axioms Erdos287.FullAnalyticKernel.budget_nonneg
#print axioms Erdos287.FullAnalyticKernel.zeroValues_input
#print axioms Erdos287.FullAnalyticKernel.analyticInput_is_a_genuine_constraint
#print axioms Erdos287.FullAnalyticKernel.analyticInput_not_from_source_combinatorics
#print axioms Erdos287.FullAnalyticKernel.analyticInput_not_inhabited_here

/-! ## §2  The master-source → typed-Perron-packets compiler -/

#print axioms Erdos287.MasterSourcePackets.chain_is_linear
#print axioms Erdos287.MasterSourcePackets.chain_indices_distinct
#print axioms Erdos287.MasterSourcePackets.chain_starts_at_physical_source
#print axioms Erdos287.MasterSourcePackets.chain_ends_at_owner_tags
#print axioms Erdos287.MasterSourcePackets.omega_inserted_only_after_two_copies
#print axioms Erdos287.MasterSourcePackets.owner_tags_are_last
#print axioms Erdos287.MasterSourcePackets.K0SP2Params.fullSmooth_eq_four_sectors
#print axioms Erdos287.MasterSourcePackets.K0SP2Params.deRegularisation_identity
#print axioms Erdos287.MasterSourcePackets.owner_type_is_exactly_six
#print axioms Erdos287.MasterSourcePackets.owner_type_exhaustive
#print axioms Erdos287.MasterSourcePackets.PacketFamily.packet_has_one_owner
#print axioms Erdos287.MasterSourcePackets.PacketFamily.no_packet_has_two_owners
#print axioms Erdos287.MasterSourcePackets.PacketFamily.owner_fibres_disjoint
#print axioms Erdos287.MasterSourcePackets.PacketFamily.owner_partition_exhaustive
#print axioms Erdos287.MasterSourcePackets.PacketFamily.owner_partition_card
#print axioms Erdos287.MasterSourcePackets.PacketFamily.owner_accounts_reassemble
#print axioms Erdos287.MasterSourcePackets.PacketFamily.packets_emitted_after_omega
#print axioms Erdos287.MasterSourcePackets.owner_tags_carry_no_analytic_bound
#print axioms Erdos287.MasterSourcePackets.compiler_does_not_inhabit_analytic_input

/-! ## §3  The one-bounded source factorisation -/

#print axioms Erdos287.OneBoundedFactor.SourceFactorData.norm_moebius_le_one
#print axioms Erdos287.OneBoundedFactor.SourceFactorData.norm_Afactor_le_one
#print axioms Erdos287.OneBoundedFactor.SourceFactorData.norm_Bfactor_le_one
#print axioms Erdos287.OneBoundedFactor.SourceFactorData.bilinear_factorisation
#print axioms Erdos287.OneBoundedFactor.SourceFactorData.bilinear_trivial_bound
#print axioms Erdos287.OneBoundedFactor.SourceFactorData.BfactorGen_moebius
#print axioms Erdos287.OneBoundedFactor.SourceFactorData.BfactorGen_add
#print axioms Erdos287.OneBoundedFactor.SourceFactorData.BfactorGen_smul
#print axioms Erdos287.OneBoundedFactor.SourceFactorData.bilinear_linear_in_moebius_slot
#print axioms
  Erdos287.OneBoundedFactor.SourceFactorData.general_coefficients_do_not_fit_the_A_slot

/-! ## §4  The determinant-one compiler -/

#print axioms Erdos287.DeterminantOne.det1_shift
#print axioms Erdos287.DeterminantOne.det1_isCoprime
#print axioms Erdos287.DeterminantOne.det1_base_of_isCoprime
#print axioms Erdos287.DeterminantOne.det1_param_complete
#print axioms Erdos287.DeterminantOne.det1_solution_line
#print axioms Erdos287.DeterminantOne.det1_t_is_unique
#print axioms Erdos287.DeterminantOne.t_line_is_unbounded

/-! ## §5  The two-copy router and the proof-local `Ω` -/

#print axioms Erdos287.TwoCopyRouter.route_eq_c0_iff
#print axioms Erdos287.TwoCopyRouter.route_eq_transverse_iff
#print axioms Erdos287.TwoCopyRouter.route_eq_bDiagonal_iff
#print axioms Erdos287.TwoCopyRouter.router_exhaustive
#print axioms Erdos287.TwoCopyRouter.router_disjoint
#print axioms Erdos287.TwoCopyRouter.routerOwner_injective
#print axioms Erdos287.TwoCopyRouter.tag_carries_no_bound
#print axioms Erdos287.TwoCopyRouter.omegaVal_le_one
#print axioms Erdos287.TwoCopyRouter.omega_partition_of_unity
#print axioms Erdos287.TwoCopyRouter.omega_partition_two_copy
#print axioms Erdos287.TwoCopyRouter.omega_is_inserted_after_two_copies
#print axioms Erdos287.TwoCopyRouter.omega_depends_on_both_copies

/-! ## §6  Analytic input → correlation, source pin, FCL channels -/

#print axioms Erdos287.FullAnalyticKernelFCL.fullCorrelation_bound_of_analyticInput
#print axioms Erdos287.FullAnalyticKernelFCL.ownerValues_sum
#print axioms Erdos287.FullAnalyticKernelFCL.physicalCorrelation_error_bound
#print axioms Erdos287.FullAnalyticKernelFCL.correlation_compiler_needs_the_analytic_input
#print axioms Erdos287.FullAnalyticKernelFCL.PhysicalCertificateSource.toData
#print axioms Erdos287.FullAnalyticKernelFCL.physicalSourcePin_not_automatic
#print axioms Erdos287.FullAnalyticKernelFCL.pinned_source_has_positive_B
#print axioms Erdos287.FullAnalyticKernelFCL.FCLErrorChannels.total_identity
#print axioms Erdos287.FullAnalyticKernelFCL.FCLErrorChannels.total_regroup
#print axioms Erdos287.FullAnalyticKernelFCL.FCLErrorChannels.each_channel_is_load_bearing
#print axioms Erdos287.FullAnalyticKernelFCL.fcl_prime_mass_pos_of_channels
#print axioms Erdos287.FullAnalyticKernelFCL.channel_budget_gives_the_literal_inequality
#print axioms Erdos287.FullAnalyticKernelFCL.channel_budget_not_constructed
#print axioms Erdos287.FullAnalyticKernelFCL.margin_delta_is_reused_not_reproved
#print axioms Erdos287.FullAnalyticKernelFCL.fcl_to_windowPair_is_reused_not_reproved
#print axioms Erdos287.FullAnalyticKernelFCL.effective_windowPair_still_open

/-! ## §7  The status layer -/

#print axioms
  Erdos287.FullAnalyticKernelImportFrontierStatus.fullAnalyticKernelImportFrontier_is_later
#print axioms Erdos287.FullAnalyticKernelImportFrontierStatus.earlier_layer_retained_unchanged
#print axioms
  Erdos287.FullAnalyticKernelImportFrontierStatus.masterSource_compiler_row_is_kernel_proved
#print axioms
  Erdos287.FullAnalyticKernelImportFrontierStatus.deRegularisation_row_is_kernel_proved
#print axioms
  Erdos287.FullAnalyticKernelImportFrontierStatus.owner_partition_row_is_kernel_proved
#print axioms Erdos287.FullAnalyticKernelImportFrontierStatus.det1_row_is_kernel_proved
#print axioms Erdos287.FullAnalyticKernelImportFrontierStatus.router_row_is_kernel_proved
#print axioms Erdos287.FullAnalyticKernelImportFrontierStatus.omega_row_is_kernel_proved
#print axioms Erdos287.FullAnalyticKernelImportFrontierStatus.oneBounded_row_is_kernel_proved
#print axioms Erdos287.FullAnalyticKernelImportFrontierStatus.fclChannels_row_is_kernel_proved
#print axioms
  Erdos287.FullAnalyticKernelImportFrontierStatus.fclToWindowPair_row_is_kernel_proved_conditional
#print axioms Erdos287.FullAnalyticKernelImportFrontierStatus.analytic_rows_are_external
#print axioms Erdos287.FullAnalyticKernelImportFrontierStatus.source_pin_row_is_open
#print axioms
  Erdos287.FullAnalyticKernelImportFrontierStatus.first_open_node_is_the_literal_fcl_source_input
#print axioms Erdos287.FullAnalyticKernelImportFrontierStatus.downstream_rows_open
#print axioms Erdos287.FullAnalyticKernelImportFrontierStatus.no_row_is_a_proof_claim

end FullAnalyticKernelImportAxiomAudit
end Erdos287
