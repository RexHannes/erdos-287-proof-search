import Mathlib
import RequestProject.Status.Erdos287V21Status

/-!
# Erdős #287 — V21 axiom audit

`#print axioms` for every principal V21 declaration.  Only `propext`, `Classical.choice`
and `Quot.sound` may appear.  No `axiom`, `opaque`, `unsafe`, `native_decide` or
`@[implemented_by]` occurs anywhere in the V21 bank, and no source or external analytic
interface is inhabited.
-/

namespace Erdos287
namespace V21Audit

section AxiomAudit

-- Two-high-projector algebra
#print axioms Erdos287.V21TwoProj.highIndicator_eq_one_sub_badIndicator
#print axioms Erdos287.V21TwoProj.twoHighProjector_pointwise
#print axioms Erdos287.V21TwoProj.high_bad_disjoint
#print axioms Erdos287.V21TwoProj.high_union_bad
#print axioms Erdos287.V21TwoProj.high_card_add_bad_card
#print axioms Erdos287.V21TwoProj.twoProjector_no_double_counting
#print axioms Erdos287.V21TwoProj.HH3221_eq_indicator_sum
#print axioms Erdos287.V21TwoProj.highHighSum_eq_AA_sub_BA_sub_AB_add_BB
#print axioms Erdos287.V21TwoProj.preProjectorVariance_eq_AA
#print axioms Erdos287.V21TwoProj.preProjectorVariance_eq_xiForm
#print axioms Erdos287.V21TwoProj.preProjectorVariance_highSet_support
#print axioms Erdos287.V21TwoProj.ambientCompat_of_source
#print axioms Erdos287.V21TwoProj.ambientCompat_not_automatic
#print axioms Erdos287.V21TwoProj.highHigh_decomposition_under_ambientCompat
#print axioms Erdos287.V21TwoProj.VhiHigh_eq_channels
#print axioms Erdos287.V21TwoProj.AAChannel_eq_weighted_preProjectorVariance

-- Five-box double orthogonality
#print axioms Erdos287.V21DoubleOrth.sign_sq_iff
#print axioms Erdos287.V21DoubleOrth.affine_congruence_iff_dvd
#print axioms Erdos287.V21DoubleOrth.affine_divisor_sign_pos
#print axioms Erdos287.V21DoubleOrth.affine_divisor_sign_neg
#print axioms Erdos287.V21DoubleOrth.fullFull_orthogonality_left
#print axioms Erdos287.V21DoubleOrth.fullFull_orthogonality_right
#print axioms Erdos287.V21DoubleOrth.doubleOrthogonality_affineDivisor
#print axioms Erdos287.V21DoubleOrth.doubleOrthogonality_congruence
#print axioms Erdos287.V21DoubleOrth.doubleOrthogonality_shift_exists
#print axioms Erdos287.V21DoubleOrth.doubleOrthogonality_coprime
#print axioms Erdos287.V21DoubleOrth.char_fiveProduct
#print axioms Erdos287.V21DoubleOrth.fiveBox_shift_exists

-- Safe bad-character count
#print axioms Erdos287.V21BadCount.badCharacter_card_le_sum_totient
#print axioms Erdos287.V21BadCount.badCharacter_card_le_triangular
#print axioms Erdos287.V21BadCount.badCharacter_card_le_triangular_div
#print axioms Erdos287.V21BadCount.badCharacter_card_le_sq
#print axioms Erdos287.V21BadCount.highSetOf_badSet_eq_highSet
#print axioms Erdos287.V21BadCount.dirichletBad_card_le_sq

-- Prime-box normalisation and the phase lemma
#print axioms Erdos287.V21PrimeBox.primeBoxNormalization_not_automatic
#print axioms Erdos287.V21PrimeBox.primeBoxL1_of_pointwise_and_count
#print axioms Erdos287.V21PrimeBox.aligningPhase_norm
#print axioms Erdos287.V21PrimeBox.aligningPhase_mul
#print axioms Erdos287.V21PrimeBox.phaseUniformBound_implies_sum_abs_omega_le_seven
#print axioms Erdos287.V21PrimeBox.phaseUniformBound_implies_each_abs_omega_le_seven
#print axioms Erdos287.V21PrimeBox.phaseUniformBound_not_automatic

-- Short-shift geometry and the external sieve interface
#print axioms Erdos287.V21Sieve.shortShiftGeometry_of_doubleOrthogonality
#print axioms Erdos287.V21Sieve.sieveDimension_eq_one
#print axioms Erdos287.V21Sieve.sieveLevelExponent_value
#print axioms Erdos287.V21Sieve.shortShiftSieve_not_automatic

-- Shiu interface and the local factor
#print axioms Erdos287.V21Shiu.totient_two_mul_of_odd
#print axioms Erdos287.V21Shiu.shiuLocalFactor_eq
#print axioms Erdos287.V21Shiu.shiuInput_localFactor_collapsed
#print axioms Erdos287.V21Shiu.shiuInput_not_automatic

-- Shared cutoff
#print axioms Erdos287.V21Cutoff.cutoffCompat_cutoffs_match
#print axioms Erdos287.V21Cutoff.cutoffCompat_unaccounted_invariant
#print axioms Erdos287.V21Cutoff.cutoffCompat_matches_v20_comparison
#print axioms Erdos287.V21Cutoff.cutoffCompat_does_not_fix_B0
#print axioms Erdos287.V21Cutoff.cutoffCompat_not_automatic

-- Exponent ledger, log budget, physical prefactor
#print axioms Erdos287.V21LogBudget.physicalShiftScale_exponent
#print axioms Erdos287.V21LogBudget.twoProjector_naturalExponent
#print axioms Erdos287.V21LogBudget.outerCauchy_exponent
#print axioms Erdos287.V21LogBudget.physicalSquareRoot_exponent
#print axioms Erdos287.V21LogBudget.exponent_ledger
#print axioms Erdos287.V21LogBudget.channel_bound_relax
#print axioms Erdos287.V21LogBudget.highVarianceLogCompiler
#print axioms Erdos287.V21LogBudget.outerCauchyLogCompiler
#print axioms Erdos287.V21LogBudget.prefactor_enters_log_ledger
#print axioms Erdos287.V21LogBudget.physicalLogPrefactor_not_automatic

-- Ownership and the outer two-prime block
#print axioms Erdos287.V21Outer.outerInnerBox_disjoint
#print axioms Erdos287.V21Outer.outerInnerBox_cover
#print axioms Erdos287.V21Outer.sevenBox_partition_cardinality
#print axioms Erdos287.V21Outer.primeDensity_no_double_spending
#print axioms Erdos287.V21Outer.parametricOwnership
#print axioms Erdos287.V21Outer.alphaOuter_labelled_swap
#print axioms Erdos287.V21Outer.alphaOuter_l1_le
#print axioms Erdos287.V21Outer.outerL2_of_sup_and_l1
#print axioms Erdos287.V21Outer.outerL2_input_of_sup_and_l1
#print axioms Erdos287.V21Outer.outerTwoPrimeL2_not_automatic

-- The conditional compilers and the non-vacuity bank
#print axioms Erdos287.V21Compiler.channelBounds_compile_to_min
#print axioms Erdos287.V21Compiler.twoHighProjector3221_closes_logVar
#print axioms Erdos287.V21Compiler.logVar_of_twoHighProjectorPackage
#print axioms Erdos287.V21Compiler.balancedSeven_of_v21_package
#print axioms Erdos287.V21Compiler.sixthMoment_not_needed_if_twoProjectorClosed
#print axioms Erdos287.V21Compiler.primeBoxNormalization_not_automatic_v21
#print axioms Erdos287.V21Compiler.shortShiftSieve_not_automatic_v21
#print axioms Erdos287.V21Compiler.shiuInput_not_automatic_v21
#print axioms Erdos287.V21Compiler.cutoffCompat_not_automatic_v21
#print axioms Erdos287.V21Compiler.physicalLogPrefactor_not_automatic_v21
#print axioms Erdos287.V21Compiler.outerTwoPrimeL2_not_automatic_v21
#print axioms Erdos287.V21Compiler.twoProjectorCompiler_cannot_construct_primeBoxNormalization
#print axioms Erdos287.V21Compiler.twoProjectorCompiler_cannot_construct_comparison
#print axioms Erdos287.V21Compiler.balancedSevenV21_cannot_construct_comparison

-- The V21 ledger
#print axioms Erdos287.V21Status.v20_hhh_route_not_controlling_v21
#print axioms Erdos287.V21Status.oldHHH_closure_proof_retracted
#print axioms Erdos287.V21Status.v21_twoProjector_route_controlling
#print axioms Erdos287.V21Status.first_exact_residual_is_primeBoxNormalization
#print axioms Erdos287.V21Status.comparison_not_first_residual
#print axioms Erdos287.V21Status.external_interfaces_uninhabited
#print axioms Erdos287.V21Status.logVar_open_conditional
#print axioms Erdos287.V21Status.sixthMoment_open_stronger_fallback
#print axioms Erdos287.V21Status.terminal_nodes_open_v21

end AxiomAudit

end V21Audit
end Erdos287
