import RequestProject.Status.CurrentStatusErdos287SupersqrtFrontier

/-!
# Axiom audit — Erdős #287 semantic repair + super-square-root frontier

`#print axioms` for every principal theorem of this append-only delta.  The build log must
show only `propext`, `Classical.choice`, `Quot.sound` (or nothing at all); in particular no
`sorryAx` and no user axiom.  No external analytic number theory is encoded as an axiom
anywhere in this layer: the analytic statements appear only as *uninhabited* interfaces.
-/

namespace Erdos287
namespace SupersqrtFrontierAudit

open Erdos287.SemanticRepair
open Erdos287.RepeatedPrime
open Erdos287.WeightedSP2
open Erdos287.BComparisonV2
open Erdos287.CenteredQCell
open Erdos287.Supersqrt3221
open Erdos287.SupersqrtFrontier
open Erdos287.SupersqrtFrontierStatus

/-! ## §1  Semantic repair: `hStar` surrogate vs literal Ford `H` -/

#print axioms hStar_not_physicalSource
#print axioms strictCollapse_not_physicalSource
#print axioms combinatorial_hStar_is_surrogate
#print axioms powerset_filter_card_le
#print axioms sum_over_small_subsets
#print axioms altSum_small_subsets_seven
#print axioms moebius_prod_primes
#print axioms prod_subset_injOn
#print axioms squarefree_prod_primes
#print axioms divisors_prod_primes
#print axioms truncMobius_depthCut_eq_neg_twenty
#print axioms fordH_physical_eq_neg_twenty
#print axioms combinatorial_hStar_does_not_construct_FordHPhysicalBinding
#print axioms fordHPhysicalBinding_not_automatic

/-! ## §2  Strict-collapse semantic repair -/

#print axioms strict_collapse_of_physicalCollapse
#print axioms strictCellHypotheses_of_physicalCollapse
#print axioms abstract_collapse_does_not_give_physicalCollapse

/-! ## §3  Repeated-prime sector, included exactly -/

#print axioms distinctPrimeCount_le_seven
#print axioms distinctPrimeCount_eq_seven_iff
#print axioms distinctPrimeCount_lt_seven_of_repeat
#print axioms Hrepeat_eq_range_four
#print axioms alternating_partial_choose_sum
#print axioms Hrepeat_eq_neg_choose
#print axioms Hrepeat_table
#print axioms HrepeatOfVector_of_injective
#print axioms countermodel_every_vector_repeats
#print axioms repeatedPrimeZero_changes_total_mass
#print axioms repeated_prime_sector_included_exactly

/-! ## §4  Weighted SP-2 physical slot source and the weighted pushforward -/

#print axioms omegaPhysical_eq_zero_of_not_mem
#print axioms omegaPhysical_of_mem
#print axioms omegaPhysical_eq_omegaBox
#print axioms norm_omegaPhysical_le_one
#print axioms omegaPhysical_support
#print axioms omegaPhysical_support_needs_profile
#print axioms omegaPhysical_eq_sp2Omega_of_trivial
#print axioms weighted_omega_ne_bare_indicator
#print axioms weightedAdapter_pointwise
#print axioms weightedAdapter_support
#print axioms weightedAdapter_not_automatic
#print axioms omegaSharpPhysical_pushforward
#print axioms omegaSharpPhysical_one_not_automatic

/-! ## §5  Finite `Bsrc` source and the V2 `B`-comparison normalisation -/

#print axioms Bsrc_eq_BofP
#print axioms localCorrection_pos
#print axioms localCorrection_le_two
#print axioms correction_pos
#print axioms oddPrimeDivisors_card_le
#print axioms correction_le_128
#print axioms Bsrc_pos
#print axioms Bsrc_lt_128
#print axioms correction_le_of_large_primes
#print axioms Bsrc_lt_two_of_large_primes
#print axioms v2_shape_of_old_shape
#print axioms v2_shape_does_not_imply_old_shape
#print axioms aggregatePrincipalV2_of_old
#print axioms aggregateUniformityV2_of_old
#print axioms twoBIndependentV2_of_old
#print axioms aggregatePrincipalV2_not_automatic
#print axioms aggregateUniformityV2_not_automatic
#print axioms twoBIndependentV2_not_automatic
#print axioms bComparison_analytic_is_not_kernel_proved

/-! ## §6  Centered `q`-cell, orthogonality, seven-slot character product -/

#print axioms centeredQCell_dvd_iff
#print axioms centeredQCell_of_dvd
#print axioms centeredQCell_of_not_dvd
#print axioms conj_char_eq_char_inv
#print axioms centeredQCell_character_expansion
#print axioms sevenSlot_character_product
#print axioms cellVectors_contains_repeats

/-! ## §7  Literal `2 + 5` split and inverse-sampled `3221` dictionary -/

#print axioms outerLabels_eq_outerBoxes
#print axioms innerLabels_eq_innerBoxes
#print axioms outer_inner_disjoint
#print axioms outer_union_inner
#print axioms outer_mul_inner_eq_pushforward
#print axioms supersqrt_inverseSampled_dictionary
#print axioms supersqrt_split_dictionary
#print axioms slotTransform_eq_blockSum
#print axioms sevenSlot_eq_outerPair_mul_fiveBox
#print axioms physical_sevenSlot_source_factorisation
#print axioms alphaOuter_sup_le
#print axioms alphaPhysical_sup_le
#print axioms alphaPhysical_l1_le
#print axioms alphaPhysical_l2_le
#print axioms outerL2_physical_needs_prime_density

/-! ## §8  Centered source compiler, sub-sqrt and super-sqrt interfaces -/

#print axioms centered_eq_raw_sub_principal
#print axioms rawSum_eq_vonMangoldt
#print axioms centered_source_identity
#print axioms centered_source_compiler_of_BV2
#print axioms subSqrt_compiler
#print axioms subSqrt_input_not_automatic
#print axioms supersqrt_route_is_sign_blind
#print axioms supersqrt_route_not_sign_aware
#print axioms supersqrt_firstCauchy_sign_firewall
#print axioms supersqrt_input_not_automatic
#print axioms supersqrt_residual_nonneg
#print axioms generatedTypeII_of_owner_chain
#print axioms owner_chain_does_not_construct_supersqrt_input

/-! ## §9  Status layer -/

#print axioms erdos287_open
#print axioms supersqrt45_open
#print axioms fullSourceKernel_open
#print axioms windowPair_open
#print axioms bComparison_analyticBanked
#print axioms bComparison_not_kernelProved
#print axioms subSqrt_not_kernelProved
#print axioms superseded_rows_not_retracted
#print axioms analytic_nodes_not_kernelProved
#print axioms backing_hStar_surrogate
#print axioms backing_hStar_firewall
#print axioms backing_fordH_conditional
#print axioms backing_collapse_split
#print axioms backing_weighted_slot_source
#print axioms backing_omegaSharpPhysical
#print axioms backing_repeated_prime
#print axioms backing_repeated_prime_routing_superseded
#print axioms backing_Bsrc
#print axioms backing_normalisation_firewall
#print axioms backing_centered_qCell
#print axioms backing_sevenSlot_product
#print axioms backing_two_plus_five
#print axioms backing_inverseSampled
#print axioms backing_centered_source_identity
#print axioms guard_supersqrt_uninhabited
#print axioms guard_subSqrt_uninhabited
#print axioms guard_sign_blind
#print axioms guard_erdos287_still_open

/-! ## §10  Corrected physical bridge `V2` -/

open Erdos287.PhysicalBridgeV2 in
#print axioms bridgeV2_slot_pointwise
open Erdos287.PhysicalBridgeV2 in
#print axioms bridgeV2_fordH_eq_neg_twenty
open Erdos287.PhysicalBridgeV2 in
#print axioms bridgeV2_weight_lt_128
open Erdos287.PhysicalBridgeV2 in
#print axioms bridgeV2_repeated_included
open Erdos287.PhysicalBridgeV2 in
#print axioms bridgeV2_not_automatic
open Erdos287.PhysicalBridgeV2 in
#print axioms oldBridge_slotWeight_is_not_v2_slotWeight
open Erdos287.PhysicalBridgeV2 in
#print axioms bridgeV2_supplies_no_rank_one
open Erdos287.PhysicalBridgeV2 in
#print axioms bridgeV2_needs_physical_fordH
#print axioms backing_bridgeV2_uninhabited

/-! ## §11  `V20` / `V21` route status -/

#print axioms v20_gram_object_valid
#print axioms v20_closure_retracted
#print axioms v21_is_controlling
#print axioms authoritative_route_is_not_v20

end SupersqrtFrontierAudit
end Erdos287
