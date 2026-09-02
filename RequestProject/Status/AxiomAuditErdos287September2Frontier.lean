import RequestProject.Status.CurrentStatusErdos287September2Frontier

/-!
# Axiom audit — the September-2 frontier and the RUN1B d*wp provider

This module is **append-only**.  It runs `#print axioms` on every principal new declaration
of this layer.  The expected output for each is the ordinary Mathlib set

```
[propext, Classical.choice, Quot.sound]
```

or a subset of it.  No custom axiom, no `sorryAx`, no `native_decide`, no `unsafe`, no
`opaque`, no `implemented_by` and no `debug.skipKernelTC` occurs anywhere in the new modules.
-/

namespace Erdos287
namespace September2FrontierAxiomAudit

#print axioms Run1B.Characters.eAdd_add
#print axioms Run1B.Characters.eAdd_eq_one_iff
#print axioms Run1B.Characters.eAdd_congr_of_modEq
#print axioms Run1B.Characters.eAdd_natMul
#print axioms Run1B.Characters.eAdd_pow_self
#print axioms Run1B.Characters.eAdd_orthogonality
#print axioms Run1B.Characters.eAdd_conj
#print axioms Run1B.Characters.eAdd_mul_conj
#print axioms Run1B.Characters.eAdd_norm_one
#print axioms Run1B.Source.q_coprime_r
#print axioms Run1B.Source.q_pos
#print axioms Run1B.Source.DW_between
#print axioms Run1B.Source.dwpSource_inhabited
#print axioms Run1B.Source.sampleSource_dwpSum
#print axioms Run1B.Source.dwpSource_does_not_carry_the_contraction
#print axioms Run1B.EffectiveModulus.sGcd_pos
#print axioms Run1B.EffectiveModulus.sGcd_dvd_r
#print axioms Run1B.EffectiveModulus.sGcd_dvd_A
#print axioms Run1B.EffectiveModulus.r_factorisation
#print axioms Run1B.EffectiveModulus.A_factorisation
#print axioms Run1B.EffectiveModulus.rSharp_pos
#print axioms Run1B.EffectiveModulus.rSharp_dvd_r
#print axioms Run1B.EffectiveModulus.gcd_ASharp_rSharp
#print axioms Run1B.EffectiveModulus.eAdd_effective_modulus
#print axioms Run1B.EffectiveModulus.invMod_spec
#print axioms Run1B.EffectiveModulus.invMod_descent
#print axioms Run1B.EffectiveModulus.eAdd_effective_modulus_inverse
#print axioms Run1B.EffectiveModulus.effective_modulus_is_not_a_size_claim
#print axioms Run1B.FourierMatrix.Kmat_row_scaling
#print axioms Run1B.FourierMatrix.Kmat_col_scaling
#print axioms Run1B.FourierMatrix.mulLeft_bijective_of_coprime
#print axioms Run1B.FourierMatrix.sum_reindex_by_invertible
#print axioms Run1B.FourierMatrix.not_dvd_sub_of_lt
#print axioms Run1B.FourierMatrix.Kmat_row_orthogonality
#print axioms Run1B.FourierMatrix.Kmat_orthogonality_diagonal
#print axioms Run1B.FourierMatrix.Kmat_scaled_isometry
#print axioms Run1B.FourierMatrix.Kmat_operator_norm_sqrt
#print axioms Run1B.FourierMatrix.Kmat_normalisation_is_explicit
#print axioms Run1B.ResidueEnergy.residueFiber_card_le
#print axioms Run1B.ResidueEnergy.residueFiber_card_le_real
#print axioms Run1B.ResidueEnergy.residueFiber_card_le_of_subset
#print axioms Run1B.ResidueEnergy.pushforward_l2_inversion_invariant
#print axioms Run1B.ResidueEnergy.Kmat_symm
#print axioms Run1B.ResidueEnergy.bilinear_l2_bound
#print axioms Run1B.LargeModulus.largeModulus_contraction
#print axioms Run1B.LargeModulus.contraction_is_not_a_log_saving
#print axioms Run1B.SmallModulus.fourier_inversion
#print axioms Run1B.SmallModulus.fourier_parseval
#print axioms Run1B.SmallModulus.fourier_l1_le_sqrt_l2
#print axioms Run1B.SmallModulus.recipPhase_periodic
#print axioms Run1B.SmallModulus.recipPhase_mod
#print axioms Run1B.SmallModulus.recipPhase_expansion
#print axioms Run1B.SmallModulus.mobiusPolyPhase_is_a_genuine_constraint
#print axioms Run1B.SmallModulus.smallModulus_compiler
#print axioms Run1B.Centering.fourierCoeff_zero_eq_mean
#print axioms Run1B.Centering.centred_h_zero_cancellation
#print axioms Run1B.Centering.principal_term_is_retained
#print axioms Run1B.Centering.ramanujanSum_prime
#print axioms Run1B.SourceRouter.sourceClass_exhaustive
#print axioms Run1B.SourceRouter.route_total
#print axioms Run1B.SourceRouter.sourceClass_pairwise_distinct
#print axioms Run1B.SourceRouter.route_ignores_analytics
#print axioms Run1B.SourceRouter.route_is_surjective
#print axioms Run1B.Compiler.run1BSourceExhaustiveInput_inhabited
#print axioms Run1B.Compiler.dwp_decomposition
#print axioms Run1B.Compiler.paperInput_is_a_genuine_constraint
#print axioms Run1B.Compiler.run1B_conditional_compiler
#print axioms Run1B.Compiler.run1B_conclusion_needs_the_analytic_provider
#print axioms SharedFord.ultraSourceSubclass_exhaustive
#print axioms SharedFord.ultraSourceSubclass_card
#print axioms SharedFord.ultraInput_is_a_genuine_constraint
#print axioms SharedFord.sharedOtherParent_conditional
#print axioms SharedFord.adapters_are_independent
#print axioms SharedFord.adapters_do_not_inhabit_each_other
#print axioms SharedFord.hardU_adapter_transport
#print axioms SharedFord.hardU_adapter_not_from_name_agreement
#print axioms SharedFord.hardU_adapter_uninhabited_in_general
#print axioms Erdos287.N2ConstantsBank.XN2_lower_bound
#print axioms Erdos287.N2ConstantsBank.two_XN2_exceeds_finite_bank
#print axioms Erdos287.N2ConstantsBank.n2_finite_splice_fails
#print axioms Erdos287.N2ConstantsBank.effective_in_principle_is_not_a_usable_M0
#print axioms Erdos287.OmegaHProvenance.current_is_unresolved
#print axioms Erdos287.OmegaHProvenance.no_silent_default
#print axioms Erdos287.OmegaHProvenance.reanchoring_requires_proof_local
#print axioms Erdos287.September2FrontierStatus.paperClosed_is_not_kernelProved
#print axioms Erdos287.September2FrontierStatus.conditional_is_not_kernelProved
#print axioms Erdos287.September2FrontierStatus.erdos287_is_open
#print axioms Erdos287.September2FrontierStatus.twinPrime_is_open
#print axioms Erdos287.September2FrontierStatus.bdiagonal_hostile_downgrade
#print axioms Erdos287.September2FrontierStatus.gate1A_is_not_on_the_critical_path
#print axioms Erdos287.September2FrontierStatus.n2_splice_is_not_closed
#print axioms Erdos287.September2FrontierStatus.effectivity_rows_are_open
#print axioms Erdos287.September2FrontierStatus.no_row_is_a_proof_claim
#print axioms Erdos287.September2FrontierStatus.erdos287_depends_on_open_nodes
#print axioms Erdos287.September2FrontierStatus.gate1A_absent_from_the_graph
#print axioms Erdos287.September2FrontierStatus.open_nodes_are_retained
#print axioms Erdos287.September2FrontierStatus.no_invented_pass
#print axioms Erdos287.September2FrontierStatus.build_is_not_a_completion_claim

end September2FrontierAxiomAudit
end Erdos287
