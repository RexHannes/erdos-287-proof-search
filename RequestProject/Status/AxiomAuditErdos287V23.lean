import Mathlib
import RequestProject.Status.Erdos287V23Status

/-!
# V23 axiom audit

`#print axioms` for every principal V23 declaration.  Only `propext`, `Classical.choice` and
`Quot.sound` may appear.  No external analytic theorem enters through a user axiom, and no
V23 file contains `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or
`@[implemented_by]`.
-/

-- §1  Retraction of the old pointwise local scalar
#print axioms Erdos287.V23OldScalar.oldPointwiseLocalScalar_three
#print axioms Erdos287.V23OldScalar.oldPointwiseLocalScalar_five
#print axioms Erdos287.V23OldScalar.old_pointwise_local_scalar_not_constant
#print axioms Erdos287.V23OldScalar.oldPointwiseLocalScalarDictionary_refuted
#print axioms Erdos287.V23OldScalar.old_dictionary_has_no_inhabitant
#print axioms Erdos287.V23OldScalar.oldScalar_fixed_modulus_is_fine

-- §2  The direct SP-2 physical comparison object
#print axioms Erdos287.V23Comparison.sp2AlternatingCoefficient_eq_depthSum
#print axioms Erdos287.V23Comparison.sp2PhysicalComparison_arg
#print axioms Erdos287.V23Comparison.sp2PhysicalComparison_split
#print axioms Erdos287.V23Comparison.sp2PhysicalComparison_eq_zero_of_pointwise_match
#print axioms Erdos287.V23Comparison.sp2PhysicalComparison_bound
#print axioms Erdos287.V23Comparison.sp2PhysicalComparison_not_automatically_zero
#print axioms Erdos287.V23Comparison.sp2PhysicalComparison_congr
#print axioms Erdos287.V23Comparison.sp2PhysicalComparison_sensitive_to_B

-- §3  The μ·log q-cell algebra
#print axioms Erdos287.V23QCell.muLog_qCell_identity
#print axioms Erdos287.V23QCell.muLog_affine_qCell
#print axioms Erdos287.V23QCell.affine_qCell_arg
#print axioms Erdos287.V23QCell.two_isUnit_of_odd
#print axioms Erdos287.V23QCell.aCoeff_spec
#print axioms Erdos287.V23QCell.aCoeff_isUnit
#print axioms Erdos287.V23QCell.qCell_nonunit_impossible
#print axioms Erdos287.V23QCell.qCell_orthogonality
#print axioms Erdos287.V23QCell.qCell_indicator
#print axioms Erdos287.V23QCell.affine_qCell_indicator

-- §4  The principal q-cell and the noncircularity firewall
#print axioms Erdos287.V23Principal.mem_unitSector
#print axioms Erdos287.V23Principal.principal_qCell_eq_physical_qCell
#print axioms Erdos287.V23Principal.affine_qCell_unique_class
#print axioms Erdos287.V23Principal.sp2PhysicalTwoBIndependent_not_automatic
#print axioms Erdos287.V23Principal.principal_qCell_eq_does_not_prove_full_twoB
#print axioms Erdos287.V23Principal.principal_qCell_identity_is_unconditional

-- §5  The aggregate Euler local-factor algebra
#print axioms Erdos287.V23Euler.aggregateEuler_localFactor_offP
#print axioms Erdos287.V23Euler.aggregateEuler_localFactor_onP
#print axioms Erdos287.V23Euler.aggregateEuler_localRatio
#print axioms Erdos287.V23Euler.aggregateEuler_H0_eq_twoB
#print axioms Erdos287.V23Euler.aggregateEuler_H0_of_no_odd_divisors
#print axioms Erdos287.V23Euler.aggregateEulerPrincipal_not_automatic
#print axioms Erdos287.V23Euler.aggregateEulerUniformity_not_automatic

-- §7  The dyadic q-packet partition
#print axioms Erdos287.V23QPacket.qPacket_owner_mem
#print axioms Erdos287.V23QPacket.qPacket_owner_unique
#print axioms Erdos287.V23QPacket.qPacket_disjoint
#print axioms Erdos287.V23QPacket.qPacket_exists_unique_owner
#print axioms Erdos287.V23QPacket.qPacket_cover
#print axioms Erdos287.V23QPacket.qPacket_reassembly
#print axioms Erdos287.V23QPacket.qPacket_reassembly_needs_all_packets
#print axioms Erdos287.V23QPacket.qPartitionInput_not_automatic
#print axioms Erdos287.V23QPacket.qPacketExhaustiveness_not_automatic

-- §8–§10  Small conductor, exceptional character, effectivity firewall
#print axioms Erdos287.V23LowCond.smallConductorNegligible_is_a_restriction
#print axioms Erdos287.V23LowCond.exceptionalCharacterNegligible_is_a_restriction
#print axioms Erdos287.V23LowCond.asymptoticBalancedSeven_not_effectiveAutomatically
#print axioms Erdos287.V23LowCond.ineffective_supplies_no_threshold
#print axioms Erdos287.V23LowCond.asymptotic_and_effective_are_distinct

-- §11–§13  Sign bookkeeping and the conditional compilers
#print axioms Erdos287.V23CompilerLayer.twoSign_total
#print axioms Erdos287.V23CompilerLayer.oneSign_is_not_twoSign
#print axioms Erdos287.V23CompilerLayer.comparison_pointwise_of_inputs
#print axioms Erdos287.V23CompilerLayer.comparison_bound_of_inputs
#print axioms Erdos287.V23CompilerLayer.balancedSevenComparison_of_inputs
#print axioms Erdos287.V23CompilerLayer.balancedSevenAsymptotic_of_closure_and_comparison
#print axioms Erdos287.V23CompilerLayer.comparisonInputs_not_automatic
#print axioms Erdos287.V23CompilerLayer.comparisonCompiler_does_not_prove_balancedSeven

-- V23 status ledger
#print axioms Erdos287.V23Status.old_pointwise_local_scalar_retracted
#print axioms Erdos287.V23Status.statuses_are_not_conflated
#print axioms Erdos287.V23Status.audit_verified_layer
#print axioms Erdos287.V23Status.audit_unverified_layer
#print axioms Erdos287.V23Status.first_audit_residuals
#print axioms Erdos287.V23Status.census_not_promoted
#print axioms Erdos287.V23Status.effectivity_statuses_separate
#print axioms Erdos287.V23Status.v23_terminal_nodes_open
#print axioms Erdos287.V23Status.v23_no_interface_inhabited
