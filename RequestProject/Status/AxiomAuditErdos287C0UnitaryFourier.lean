import Mathlib
import RequestProject.Status.CurrentStatusErdos287TransverseCarrier

/-!
# Axiom audit — Erdős #287, C0 unitary-Fourier / transverse-carrier Δ

`#print axioms` for every declaration of this delta.

Allowed inherited axioms only:

```
propext, Classical.choice, Quot.sound
```

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `implemented_by` occurs as
a code construct in any module of this delta; those words appear only inside docstring prose.
Decidable ledger facts are discharged with `decide +kernel`.

The conditional statements (`threeCarrierReciprocalFourier_of_productEnergy`,
`c0_balanced_branch_bound_of`, `perronNuclear_total_of_normalisation`,
`omegaHL2_of_pointwise_normalisation`, `transverseTwoCarrier_bound_of_unitSupport`,
`transverseTwoCarrier_bound_with_fibre_weights`) depend only on their explicitly named
hypotheses; each hypothesis shell is proved non-automatic, so nothing is silently discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace C0UnitaryFourierAudit

/-! ## Reciprocal unitary Fourier core (unconditional) -/

#print axioms Erdos287.ReciprocalUnitaryFourier.norm_sum_mul_sq_le
#print axioms Erdos287.ReciprocalUnitaryFourier.unitaryFourierKernel
#print axioms Erdos287.ReciprocalUnitaryFourier.unitaryFourierKernel_symm
#print axioms Erdos287.ReciprocalUnitaryFourier.unitaryFourierKernel_norm
#print axioms Erdos287.ReciprocalUnitaryFourier.unitaryFourier_mulConj_sum
#print axioms Erdos287.ReciprocalUnitaryFourier.unitaryFourier_column_energy
#print axioms Erdos287.ReciprocalUnitaryFourier.unitaryFourier_bilinear_bound
#print axioms Erdos287.ReciprocalUnitaryFourier.unitaryFourier_finset_bilinear_bound
#print axioms Erdos287.ReciprocalUnitaryFourier.isUnit_zmod_inv
#print axioms Erdos287.ReciprocalUnitaryFourier.zmod_inv_inv_of_isUnit
#print axioms Erdos287.ReciprocalUnitaryFourier.zmod_inv_bijOn_units
#print axioms Erdos287.ReciprocalUnitaryFourier.reciprocalUnitaryFourier_bilinear_bound
#print axioms Erdos287.ReciprocalUnitaryFourier.transverseTwoCarrierUnitaryFourier
#print axioms Erdos287.ReciprocalUnitaryFourier.unitaryFourier_mulConj_sum_composite

/-! ## Balanced-b compiler, residue aggregation, contraction identity, coprime firewall -/

#print axioms Erdos287.BalancedBUnitaryFourier.norm_sum_sq_le_card
#print axioms Erdos287.BalancedBUnitaryFourier.residueAggregate
#print axioms Erdos287.BalancedBUnitaryFourier.residueAggregate_l2_le_maxFiber
#print axioms Erdos287.BalancedBUnitaryFourier.interval_residue_fibre_card_le
#print axioms Erdos287.BalancedBUnitaryFourier.intervalResidueAggregate_l2_bound
#print axioms Erdos287.BalancedBUnitaryFourier.reciprocalPhase_fiberwise
#print axioms Erdos287.BalancedBUnitaryFourier.balancedReciprocalFourier_compiler
#print axioms Erdos287.BalancedBUnitaryFourier.balancedFourier_contraction_identity
#print axioms Erdos287.BalancedBUnitaryFourier.coprime_product_left
#print axioms Erdos287.BalancedBUnitaryFourier.coprime_product_middle
#print axioms Erdos287.BalancedBUnitaryFourier.coprime_product_right
#print axioms Erdos287.BalancedBUnitaryFourier.coprime_product_all
#print axioms Erdos287.BalancedBUnitaryFourier.ProductConvolutionEnergyHypothesis
#print axioms Erdos287.BalancedBUnitaryFourier.productConvolutionEnergy_not_automatic
#print axioms Erdos287.BalancedBUnitaryFourier.threeCarrierReciprocalFourier_of_productEnergy

/-! ## Affine / bilinear moving numerator algebra (unconditional) -/

#print axioms Erdos287.AffineBilinearReciprocalNumerator.zmod_inv_mul_of_isUnit
#print axioms Erdos287.AffineBilinearReciprocalNumerator.affineNumerator_reciprocal_decomposition
#print axioms Erdos287.AffineBilinearReciprocalNumerator.affineBilinearNumerator_reciprocal_decomposition
#print axioms Erdos287.AffineBilinearReciprocalNumerator.affineBilinearNumerator_character_factorisation
#print axioms Erdos287.AffineBilinearReciprocalNumerator.affineNumerator_character_factorisation
#print axioms Erdos287.AffineBilinearReciprocalNumerator.affineBilinear_rankOne_reduction

/-! ## C0 physical normalisation interface (source pins, conditional compiler) -/

#print axioms Erdos287.C0PhysicalNormalisation.PerronNuclearNormalisationHypothesis
#print axioms Erdos287.C0PhysicalNormalisation.perronNuclear_total_of_normalisation
#print axioms Erdos287.C0PhysicalNormalisation.perronNuclearNormalisation_not_automatic
#print axioms Erdos287.C0PhysicalNormalisation.OmegaHL2NormalisationHypothesis
#print axioms Erdos287.C0PhysicalNormalisation.omegaHL2_of_pointwise_normalisation
#print axioms Erdos287.C0PhysicalNormalisation.omegaHL2Normalisation_not_automatic
#print axioms Erdos287.C0PhysicalNormalisation.C0PhysicalNormalisationHypothesis
#print axioms Erdos287.C0PhysicalNormalisation.c0PhysicalNormalisation_not_automatic
#print axioms Erdos287.C0PhysicalNormalisation.c0PhysicalNormalisation_satisfiable
#print axioms Erdos287.C0PhysicalNormalisation.c0_balanced_branch_bound_of

/-! ## Transverse carrier interface -/

#print axioms Erdos287.TransverseCarrier.UsableTwoCarrierPair
#print axioms Erdos287.TransverseCarrier.usableTwoCarrierPair_not_automatic
#print axioms Erdos287.TransverseCarrier.usableTwoCarrierPair_satisfiable
#print axioms Erdos287.TransverseCarrier.transverseTwoCarrier_bound_of_unitSupport
#print axioms Erdos287.TransverseCarrier.transverseTwoCarrier_bound_with_fibre_weights
#print axioms Erdos287.TransverseCarrier.transverseCarrierCase_no_exhaustiveness_claimed

/-! ## C0 unitary-Fourier status layer (metadata) -/

#print axioms Erdos287.C0UnitaryFourierStatus.c0FourierLedger
#print axioms Erdos287.C0UnitaryFourierStatus.reciprocalUnitaryFourierStatus
#print axioms Erdos287.C0UnitaryFourierStatus.balancedBUnitaryFourierStatus
#print axioms Erdos287.C0UnitaryFourierStatus.exactProductInverseConvStatus
#print axioms Erdos287.C0UnitaryFourierStatus.exactProductCollisionStatus
#print axioms Erdos287.C0UnitaryFourierStatus.doubleTypeIIStatus
#print axioms Erdos287.C0UnitaryFourierStatus.c0Status
#print axioms Erdos287.C0UnitaryFourierStatus.omegaHStatus
#print axioms Erdos287.C0UnitaryFourierStatus.completePerronNormalisationStatus
#print axioms Erdos287.C0UnitaryFourierStatus.erdos287Status
#print axioms Erdos287.C0UnitaryFourierStatus.finite_fourier_rows_are_kernelProved
#print axioms Erdos287.C0UnitaryFourierStatus.only_finite_rows_are_kernelProved
#print axioms Erdos287.C0UnitaryFourierStatus.c0_not_kernelProved
#print axioms Erdos287.C0UnitaryFourierStatus.source_pins_open
#print axioms Erdos287.C0UnitaryFourierStatus.analytic_rows_are_not_kernel_rows
#print axioms Erdos287.C0UnitaryFourierStatus.retracted_architecture_stays_retracted
#print axioms Erdos287.C0UnitaryFourierStatus.erdos287_open
#print axioms Erdos287.C0UnitaryFourierStatus.productConvolutionEnergy_is_hypothesis_row
#print axioms Erdos287.C0UnitaryFourierStatus.fourier_pass_does_not_close_c0
#print axioms Erdos287.C0UnitaryFourierStatus.inv_sqrt_comparison_not_automatic
#print axioms Erdos287.C0UnitaryFourierStatus.constantRank
#print axioms Erdos287.C0UnitaryFourierStatus.DependsOn
#print axioms Erdos287.C0UnitaryFourierStatus.constant_order_acyclic
#print axioms Erdos287.C0UnitaryFourierStatus.sourceLift_ledger_still_preserved

/-! ## Transverse-carrier status layer (metadata) -/

#print axioms Erdos287.TransverseCarrierStatus.transverseLedger
#print axioms Erdos287.TransverseCarrierStatus.nextTransverseStatus
#print axioms Erdos287.TransverseCarrierStatus.only_finite_mechanism_is_kernelProved
#print axioms Erdos287.TransverseCarrierStatus.carrier_factorisation_open
#print axioms Erdos287.TransverseCarrierStatus.pair_existence_is_next_child
#print axioms Erdos287.TransverseCarrierStatus.bdiagonal_parallel_and_open
#print axioms Erdos287.TransverseCarrierStatus.transverse_branch_strictly_reduced
#print axioms Erdos287.TransverseCarrierStatus.no_double_spending
#print axioms Erdos287.TransverseCarrierStatus.c0_ledger_still_preserved

end C0UnitaryFourierAudit
end Erdos287
