import Mathlib
import RequestProject.Status.CurrentStatusErdos287Block20

/-!
# Trust audit — Erdős #287, BLOCK20 Δ safe bank

`#print axioms` over every principal declaration added by this pass.  Expected output for
each: a subset of `propext`, `Classical.choice`, `Quot.sound`.

The new files contain no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or
`@[implemented_by]`, and no analytic or source socket of this pass has an inhabitant anywhere
in the repository.
-/

namespace Erdos287
namespace Block20Audit

/-! ## §2  Source-seal repair -/

#print axioms Erdos287.Block20.mem_smoothSector
#print axioms Erdos287.Block20.fixedCertificate_k0_Jempty_reduction
#print axioms Erdos287.Block20.fixedCertificate_smoothCut_reduction
#print axioms Erdos287.Block20.fixedCertificate_sevenBox_eq_neg20
#print axioms Erdos287.Block20.fixedCertificate_sevenBox_depth_metadata
#print axioms Erdos287.Block20.omegaBox_dictionary
#print axioms Erdos287.Block20.omegaBox_dictionary_negative_twist
#print axioms Erdos287.Block20.omegaBox_carries_no_vonMangoldt_factor
#print axioms Erdos287.Block20.omegaBox_carries_no_log_factor
#print axioms Erdos287.Block20.omegaBox_carries_no_inverse_log_factor
#print axioms Erdos287.Block20.vonMangoldt_sum_divisors_eq_log
#print axioms Erdos287.Block20.balancedSevenSeal_of_cellIdentity
#print axioms Erdos287.Block20.sourceSeal_residual_is_exactly_the_cell_identity
#print axioms Erdos287.Block20.sourceSeal_residual_not_automatic
#print axioms Erdos287.Block20.sourceSeal_status_is_open

/-! ## §3–§5  Ledger, packing, source split -/

#print axioms Erdos287.Block20.nu0Q_value
#print axioms Erdos287.Block20.nu0Q_ne_one_sixth
#print axioms Erdos287.Block20.sigmaStar_ge
#print axioms Erdos287.Block20.sigmaStar_pos
#print axioms Erdos287.Block20.sigmaStar_le_nu0
#print axioms Erdos287.Block20.eps_one_over_600_not_admissible
#print axioms Erdos287.Block20.nineteen_blocks_overflow
#print axioms Erdos287.Block20.blocksMass_append
#print axioms Erdos287.Block20.blocksMass_eq_flatten_sum
#print axioms Erdos287.Block20.blocksMass_ge
#print axioms Erdos287.Block20.nonfinal_block_count_le_18
#print axioms Erdos287.Block20.mem_bigAtoms
#print axioms Erdos287.Block20.mem_smallAtoms
#print axioms Erdos287.Block20.bigAtoms_append_smallAtoms_perm
#print axioms Erdos287.Block20.groupSmall_flatten
#print axioms Erdos287.Block20.groupSmall_block_ge
#print axioms Erdos287.Block20.groupSmall_leftover_lt
#print axioms Erdos287.Block20.groupSmall_block_le
#print axioms Erdos287.Block20.packSide_perm
#print axioms Erdos287.Block20.packSide_mem
#print axioms Erdos287.Block20.packSide_leftover_mem
#print axioms Erdos287.Block20.packSide_block_ge
#print axioms Erdos287.Block20.packSide_block_le
#print axioms Erdos287.Block20.packSide_leftover_lt
#print axioms Erdos287.Block20.packSide_singleton_provenance
#print axioms Erdos287.Block20.packSide_grouped_provenance
#print axioms Erdos287.Block20.packSide_mass_le
#print axioms Erdos287.Block20.packBoth_no_straddle
#print axioms Erdos287.Block20.packBoth_nonfinal_count_le_18
#print axioms Erdos287.Block20.packBoth_total_count_le_20
#print axioms Erdos287.Block20.packBoth_validity
#print axioms Erdos287.Block20.block20Validity_not_automatic
#print axioms Erdos287.Block20.block20_gcd_smooth_rough
#print axioms Erdos287.Block20.block20_smoothRough_exists
#print axioms Erdos287.Block20.bigOmega_rough_le_420
#print axioms Erdos287.Block20.truncMobius_coprime_split
#print axioms Erdos287.Block20.truncMobius_gamma_split

/-! ## §6  Large prime-power router -/

#print axioms Erdos287.Block20.largePrimePower_not_squarefree
#print axioms Erdos287.Block20.largePrimePower_squarefree_excluded
#print axioms Erdos287.Block20.largePrimePower_router_partition
#print axioms Erdos287.Block20.largePrimePower_sector_negligible_of_input
#print axioms Erdos287.Block20.largePrimePowerRouter_not_automatic

/-! ## §12  Perron sockets -/

#print axioms Erdos287.Block20.perron_separated_prefix_of_input
#print axioms Erdos287.Block20.perronConditionRemoval_not_automatic
#print axioms Erdos287.Block20.perron_constant_is_not_a_theorem
#print axioms Erdos287.Block20.boundaryRouter_preserves_literal_source
#print axioms Erdos287.Block20.smoothed_certificate_is_a_different_source
#print axioms Erdos287.Block20.perronBoundaryRouter_not_automatic

/-! ## §7–§11, §13, §14  Templates, bilinear split, generated Type-II, budget -/

#print axioms Erdos287.Block20.template_block_count_le_20
#print axioms Erdos287.Block20.template_block_card
#print axioms Erdos287.Block20.template_selectedMass_is_template_data
#print axioms Erdos287.Block20.template_selection_not_recomputed
#print axioms Erdos287.Block20.mass_dependent_selection_is_different
#print axioms Erdos287.Block20.typeII_window_from_first_crossing
#print axioms Erdos287.Block20.typeII_window_endpoint
#print axioms Erdos287.Block20.typeII_size_window
#print axioms Erdos287.Block20.template_product_split
#print axioms Erdos287.Block20.template_predicate_split
#print axioms Erdos287.Block20.template_mass_split
#print axioms Erdos287.Block20.fixed_template_source_factorisation
#print axioms Erdos287.Block20.joint_coprimality_predicate_not_factorisable
#print axioms Erdos287.Block20.generated_xi_support
#print axioms Erdos287.Block20.generated_kappa_support
#print axioms Erdos287.Block20.mobius_factor_occurs_once
#print axioms Erdos287.Block20.ordered_block_convolution
#print axioms Erdos287.Block20.generatedCoefficientNorm_attaches_to_the_generated_class
#print axioms Erdos287.Block20.generatedCoefficientNorm_not_automatic
#print axioms Erdos287.Block20.threeSmallPrime_supersession_of_coverage
#print axioms Erdos287.Block20.threeSmallPrime_class_is_nonempty
#print axioms Erdos287.Block20.block20GeneratedTypeII_not_automatic
#print axioms Erdos287.Block20.k0_uniform_fragmentation_compiler
#print axioms Erdos287.Block20.k0UniformFragmentation_not_inhabited_here
#print axioms Erdos287.Block20.generated_typeII_is_the_mainline_residual
#print axioms Erdos287.Block20.total_eq_sum_of_fields
#print axioms Erdos287.Block20.currentCrudeBudget_total
#print axioms Erdos287.Block20.crude_budget_is_not_an_optimality_theorem

/-! ## §15  Effectivity adapter -/

#print axioms Erdos287.Block20.exceptionalRoute_not_decided
#print axioms Erdos287.Block20.exceptionalAdapter_comparison
#print axioms Erdos287.Block20.effective_smallQ_lowConductor_compiler
#print axioms Erdos287.Block20.exceptionalAdapter_not_automatic
#print axioms Erdos287.Block20.effective_route_is_not_chosen

/-! ## §16  Status layer -/

#print axioms Erdos287.Block20Status.no_closed_rows
#print axioms Erdos287.Block20Status.erdos287_open
#print axioms Erdos287.Block20Status.fcl_open
#print axioms Erdos287.Block20Status.generated_typeII_is_current_mainline_residual
#print axioms Erdos287.Block20Status.effectivity_adapter_is_parallel_residual
#print axioms Erdos287.Block20Status.threeSmallPrime_not_false
#print axioms Erdos287.Block20Status.source_seal_row_is_open_with_exact_residual
#print axioms Erdos287.Block20Status.block20_finite_rows_are_theorems
#print axioms Erdos287.Block20Status.analytic_rows_are_uninhabited
#print axioms Erdos287.Block20Status.historical_balanced7_status_preserved
#print axioms Erdos287.Block20Status.log_budget_is_crude_not_optimal

end Block20Audit
end Erdos287
