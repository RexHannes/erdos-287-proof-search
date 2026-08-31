import Mathlib
import RequestProject.Status.CurrentStatusErdos287SimultaneousCritical

/-!
# Axiom audit — Erdős #287, dual-level / simultaneous-critical Δ

`#print axioms` for every declaration of this append-only delta (Bézout-row affine algebra,
Bézout three-axis finite Fourier, dual CRT split / dual-level reciprocity, dual `Ξ` reduction,
dual pairwise finite Fourier, affine-product interface, reciprocal-density duality, and the new
status ledger).

Allowed inherited axioms only:

```
propext, Classical.choice, Quot.sound
```

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `implemented_by` occurs as a
code construct in any module of this delta; those words appear only inside docstring prose.
Finite decidable facts are discharged by `decide +kernel`, `norm_num` or explicit witnesses.

The conditional compilers of this delta
(`transverseAllQAtomicGrouped_of_productEnergy`, `dualAffineProductFourier_of_energy`) carry their
analytic inputs as *visible hypotheses* (`GroupedQEnergyHypothesis`, `AffineProductEnergyBound`,
`OmegaWeightedDivisorMomentBound`, `XiGcdTailBound`), and each of those shells is accompanied by a
kernel-checked `not_automatic` theorem, so no analytic input is silently discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace DualLevelAudit

/-! ## Bézout-row affine CRT algebra -/

#print axioms Erdos287.TransverseBezoutRow.BezoutRowData
#print axioms Erdos287.TransverseBezoutRow.BezoutRowData.r
#print axioms Erdos287.TransverseBezoutRow.BezoutRowData.Mg
#print axioms Erdos287.TransverseBezoutRow.BezoutRowData.r_eq
#print axioms Erdos287.TransverseBezoutRow.BezoutRowData.r_pos
#print axioms Erdos287.TransverseBezoutRow.BezoutRowData.Mg_pos
#print axioms Erdos287.TransverseBezoutRow.BezoutRowData.cM
#print axioms Erdos287.TransverseBezoutRow.BezoutRowData.dEll
#print axioms Erdos287.TransverseBezoutRow.BezoutRowData.gammaG
#print axioms Erdos287.TransverseBezoutRow.BezoutRowData.cM_spec
#print axioms Erdos287.TransverseBezoutRow.BezoutRowData.gammaG_mod_m
#print axioms Erdos287.TransverseBezoutRow.BezoutRowData.gammaG_mod_m_inverse_free
#print axioms Erdos287.TransverseBezoutRow.BezoutRowData.gammaG_mod_r0
#print axioms Erdos287.TransverseBezoutRow.BezoutRowData.gammaG_affine_slope
#print axioms Erdos287.TransverseBezoutRow.affine_residue_unique_of_unit_slope
#print axioms Erdos287.TransverseBezoutRow.gammaG_affine_injective_mod_r0
#print axioms Erdos287.TransverseBezoutRow.gammaG_affine_injective_zmod
#print axioms Erdos287.TransverseBezoutRow.affineGcd_divisor_residue_class
#print axioms Erdos287.TransverseBezoutRow.affineGcd_solution_set_subset_class
#print axioms Erdos287.TransverseBezoutRow.affineGcd_interval_count

/-! ## Bézout three-axis frequency map and finite Fourier bound -/

#print axioms Erdos287.TransverseBezoutThreeAxis.fiberAggregate
#print axioms Erdos287.TransverseBezoutThreeAxis.fiberAggregate_l2_le_maxFiber
#print axioms Erdos287.TransverseBezoutThreeAxis.fiberAggregate_sum
#print axioms Erdos287.TransverseBezoutThreeAxis.aggregatedFourier_bilinear_bound
#print axioms Erdos287.TransverseBezoutThreeAxis.fG
#print axioms Erdos287.TransverseBezoutThreeAxis.fG_mul_q
#print axioms Erdos287.TransverseBezoutThreeAxis.fG_fibre_q_congr
#print axioms Erdos287.TransverseBezoutThreeAxis.fG_fibre_ell_congr
#print axioms Erdos287.TransverseBezoutThreeAxis.box_fibre_card_le
#print axioms Erdos287.TransverseBezoutThreeAxis.bezoutRowThreeAxisFourier_bound
#print axioms Erdos287.TransverseBezoutThreeAxis.bezoutThreeAxis_contraction_identity
#print axioms Erdos287.TransverseBezoutThreeAxis.GroupedQEnergyHypothesis
#print axioms Erdos287.TransverseBezoutThreeAxis.groupedQEnergy_not_automatic
#print axioms Erdos287.TransverseBezoutThreeAxis.transverseAllQAtomicGrouped_of_productEnergy

/-! ## Dual CRT split, additive reciprocity, dual-level reciprocity data -/

#print axioms Erdos287.TransverseDualLevel.int_modEq_combine_coprime
#print axioms Erdos287.TransverseDualLevel.int_inverse_unique
#print axioms Erdos287.TransverseDualLevel.addPhase
#print axioms Erdos287.TransverseDualLevel.addPhase_norm
#print axioms Erdos287.TransverseDualLevel.addPhase_add
#print axioms Erdos287.TransverseDualLevel.addPhase_period
#print axioms Erdos287.TransverseDualLevel.addPhase_congr
#print axioms Erdos287.TransverseDualLevel.addPhase_split
#print axioms Erdos287.TransverseDualLevel.transverseDualCRT_split_int
#print axioms Erdos287.TransverseDualLevel.transverseDualCRT_split
#print axioms Erdos287.TransverseDualLevel.additiveReciprocity_coprime
#print axioms Erdos287.TransverseDualLevel.additiveReciprocity_phase
#print axioms Erdos287.TransverseDualLevel.Cmqg
#print axioms Erdos287.TransverseDualLevel.Cmqg_mod_m
#print axioms Erdos287.TransverseDualLevel.Cmqg_mod_q
#print axioms Erdos287.TransverseDualLevel.Xi
#print axioms Erdos287.TransverseDualLevel.Xi_affine_slope
#print axioms Erdos287.TransverseDualLevel.Xi_affine_slope_mod
#print axioms Erdos287.TransverseDualLevel.DualReciprocityData
#print axioms Erdos287.TransverseDualLevel.DualReciprocityData.modulus
#print axioms Erdos287.TransverseDualLevel.DualReciprocityData.modulus_pos
#print axioms Erdos287.TransverseDualLevel.DualReciprocityData.C
#print axioms Erdos287.TransverseDualLevel.DualReciprocityData.XiOf
#print axioms Erdos287.TransverseDualLevel.DualReciprocityData.C_mod_m
#print axioms Erdos287.TransverseDualLevel.DualReciprocityData.C_mod_q
#print axioms Erdos287.TransverseDualLevel.DualReciprocityData.XiOf_affine_slope
#print axioms Erdos287.TransverseDualLevel.transverseDualLevelReciprocity
#print axioms Erdos287.TransverseDualLevel.archDual_is_a_free_parameter

/-! ## Dual Xi normal form and Xi-gcd reduction -/

#print axioms Erdos287.TransverseDualXi.dConst
#print axioms Erdos287.TransverseDualXi.dConst_dvd_mq
#print axioms Erdos287.TransverseDualXi.dConst_pos
#print axioms Erdos287.TransverseDualXi.dConst_dvd_const
#print axioms Erdos287.TransverseDualXi.dConst_dvd_slope
#print axioms Erdos287.TransverseDualXi.dConst_dvd_Xi
#print axioms Erdos287.TransverseDualXi.M0Dual
#print axioms Erdos287.TransverseDualXi.M0Dual_mul_dConst
#print axioms Erdos287.TransverseDualXi.M0Dual_pos
#print axioms Erdos287.TransverseDualXi.c0
#print axioms Erdos287.TransverseDualXi.s0
#print axioms Erdos287.TransverseDualXi.Xi0
#print axioms Erdos287.TransverseDualXi.Xi0_mul_dConst
#print axioms Erdos287.TransverseDualXi.Xi0_affine_slope
#print axioms Erdos287.TransverseDualXi.dXi
#print axioms Erdos287.TransverseDualXi.dXi_dvd_M0Dual
#print axioms Erdos287.TransverseDualXi.dXi_dvd_Xi0
#print axioms Erdos287.TransverseDualXi.dXi_pos
#print axioms Erdos287.TransverseDualXi.MPrime
#print axioms Erdos287.TransverseDualXi.XiPrime
#print axioms Erdos287.TransverseDualXi.MPrime_mul_dXi
#print axioms Erdos287.TransverseDualXi.XiPrime_mul_dXi
#print axioms Erdos287.TransverseDualXi.xiRed_coprime
#print axioms Erdos287.TransverseDualXi.xi_divisor_affine_residue_unique
#print axioms Erdos287.TransverseDualXi.constant_and_variable_xi_gcd_differ
#print axioms Erdos287.TransverseDualXi.XiGcdTailBound
#print axioms Erdos287.TransverseDualXi.xiGcdTailBound_not_automatic
#print axioms Erdos287.TransverseDualXi.xiGcdTailBound_satisfiable

/-! ## Dual frequency fibres and dual pairwise finite Fourier bounds -/

#print axioms Erdos287.TransverseDualPairwise.doubleAggregatedFourier_bound
#print axioms Erdos287.TransverseDualPairwise.fDual
#print axioms Erdos287.TransverseDualPairwise.fDual_r_unique
#print axioms Erdos287.TransverseDualPairwise.fDual_ell_unique
#print axioms Erdos287.TransverseDualPairwise.card_le_of_fibre_fst
#print axioms Erdos287.TransverseDualPairwise.card_le_of_fibre_snd
#print axioms Erdos287.TransverseDualPairwise.dualPairwise_min_of_two_counts
#print axioms Erdos287.TransverseDualPairwise.fDual_r_fibre_interval_count
#print axioms Erdos287.TransverseDualPairwise.fDual_ell_fibre_interval_count
#print axioms Erdos287.TransverseDualPairwise.dualPairwise_Delta_r_bound
#print axioms Erdos287.TransverseDualPairwise.dualPairwise_Delta_ell_bound
#print axioms Erdos287.TransverseDualPairwise.dualPairwise_ell_r_bound
#print axioms Erdos287.TransverseDualPairwise.dualPairwise_min_bound
#print axioms Erdos287.TransverseDualPairwise.dualPairwise_min_is_not_product
#print axioms Erdos287.TransverseDualPairwise.dualPairwise_contraction_identity
#print axioms Erdos287.TransverseDualPairwise.dualPairwise_contraction_identity_symmetric

/-! ## Affine-product pushforward, collision, energy interface, Omega norm pin -/

#print axioms Erdos287.TransverseAffineProduct.numerator
#print axioms Erdos287.TransverseAffineProduct.numeratorAggregate
#print axioms Erdos287.TransverseAffineProduct.affineProduct_pushforward
#print axioms Erdos287.TransverseAffineProduct.affineProduct_collision_iff
#print axioms Erdos287.TransverseAffineProduct.AffineProductEnergyBound
#print axioms Erdos287.TransverseAffineProduct.affineProductEnergy_not_automatic
#print axioms Erdos287.TransverseAffineProduct.dualAffineProductFourier_of_energy
#print axioms Erdos287.TransverseAffineProduct.OmegaWeightedDivisorMomentBound
#print axioms Erdos287.TransverseAffineProduct.omegaWeighted_not_implied_by_l2
#print axioms Erdos287.TransverseAffineProduct.omegaWeighted_satisfiable
#print axioms Erdos287.TransverseAffineProduct.SimultaneousCriticalPacket
#print axioms Erdos287.TransverseAffineProduct.simultaneousCriticalPacket_fields_unfilled

/-! ## Reciprocal-density duality identities -/

#print axioms Erdos287.ReciprocalDensityDuality.rhoOld
#print axioms Erdos287.ReciprocalDensityDuality.rhoDualPair
#print axioms Erdos287.ReciprocalDensityDuality.rhoDualFull
#print axioms Erdos287.ReciprocalDensityDuality.reciprocalDensity_product_identity
#print axioms Erdos287.ReciprocalDensityDuality.reciprocalDensity_ratio_identity
#print axioms Erdos287.ReciprocalDensityDuality.reciprocalDensity_geometric_mean_bound
#print axioms Erdos287.ReciprocalDensityDuality.reciprocalDensity_ratio_bound
#print axioms Erdos287.ReciprocalDensityDuality.scaleSaturation_sanity_instance
#print axioms Erdos287.ReciprocalDensityDuality.reciprocalDensity_duality_is_not_closure

/-! ## Dual-level / simultaneous-critical status ledger -/

#print axioms Erdos287.SimultaneousCriticalStatus.DualLevelNode
#print axioms Erdos287.SimultaneousCriticalStatus.dualLevelLedger
#print axioms Erdos287.SimultaneousCriticalStatus.bezoutThreeAxisFiniteStatus
#print axioms Erdos287.SimultaneousCriticalStatus.dualLevelReciprocityFiniteStatus
#print axioms Erdos287.SimultaneousCriticalStatus.dualPairwiseFourierFiniteStatus
#print axioms Erdos287.SimultaneousCriticalStatus.xiGcdRouterFormalStatus
#print axioms Erdos287.SimultaneousCriticalStatus.affineProductEnergyStatus
#print axioms Erdos287.SimultaneousCriticalStatus.reciprocalDensityDualityStatus
#print axioms Erdos287.SimultaneousCriticalStatus.simultaneousCriticalStatus
#print axioms Erdos287.SimultaneousCriticalStatus.bDiagonalStatus
#print axioms Erdos287.SimultaneousCriticalStatus.transverseStatus
#print axioms Erdos287.SimultaneousCriticalStatus.c0Status
#print axioms Erdos287.SimultaneousCriticalStatus.erdos287Status
#print axioms Erdos287.SimultaneousCriticalStatus.dualLevel_kernel_rows
#print axioms Erdos287.SimultaneousCriticalStatus.analytic_rows_are_not_kernel_rows
#print axioms Erdos287.SimultaneousCriticalStatus.xiGcd_router_split
#print axioms Erdos287.SimultaneousCriticalStatus.omega_norms_are_separate_pins
#print axioms Erdos287.SimultaneousCriticalStatus.simultaneousCritical_is_first_frontier
#print axioms Erdos287.SimultaneousCriticalStatus.superseded_frontiers_preserved
#print axioms Erdos287.SimultaneousCriticalStatus.crossPacket_two_axis_retracted
#print axioms Erdos287.SimultaneousCriticalStatus.mobius_sign_remains_linear
#print axioms Erdos287.SimultaneousCriticalStatus.level_typeI_typeII_status
#print axioms Erdos287.SimultaneousCriticalStatus.bdiagonal_untouched
#print axioms Erdos287.SimultaneousCriticalStatus.erdos287_open_after_dualLevel
#print axioms Erdos287.SimultaneousCriticalStatus.SimultaneousCriticalBoundary
#print axioms Erdos287.SimultaneousCriticalStatus.boundary_constraints_are_metadata
#print axioms Erdos287.SimultaneousCriticalStatus.MovableNumeratorCoordinate
#print axioms Erdos287.SimultaneousCriticalStatus.DerivedNumeratorQuantity
#print axioms Erdos287.SimultaneousCriticalStatus.movable_coordinates_are_two
#print axioms Erdos287.SimultaneousCriticalStatus.SingleCarrierAbsorption
#print axioms Erdos287.SimultaneousCriticalStatus.singleCarrier_absorbed_not_false
#print axioms Erdos287.SimultaneousCriticalStatus.oneConductor_ledger_preserved
#print axioms Erdos287.SimultaneousCriticalStatus.c0_ledger_preserved_after_dualLevel
#print axioms Erdos287.SimultaneousCriticalStatus.singleCarrier_row_of_old_ledger_not_rewritten

end DualLevelAudit
end Erdos287