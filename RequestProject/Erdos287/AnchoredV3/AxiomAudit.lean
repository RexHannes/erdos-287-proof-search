import RequestProject.Erdos287.AnchoredV3.Reconciliation
import RequestProject.Erdos287.AnchoredV3.GlobalNeutrality
import RequestProject.Erdos287.AnchoredV3.OldEmptyNewHit
import RequestProject.Erdos287.AnchoredV3.ColumnPackets
import RequestProject.Erdos287.AnchoredV3.SupportMultiplicity
import RequestProject.Erdos287.AnchoredV3.ColumnLattice
import RequestProject.Erdos287.AnchoredV3.TargetMobility

/-!
# Anchored V3 — axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Every principal exported theorem of the Anchored V3 layer is checked here with `#print axioms`.
No custom `axiom`, `sorry`, `admit`, `native_decide`, `unsafe`, `opaque` or `@[implemented_by]`
occurs anywhere in this layer; the only axioms reported are Lean's standard `propext`,
`Classical.choice` and `Quot.sound` (some theorems use fewer).  The `decide` calls used in the
finite witnesses are kernel-reducible and introduce no axiom dependency.
-/

namespace Erdos287
namespace AnchoredV3

-- A. global multiplier neutrality
#print axioms Erdos287.AnchoredV3.globalNeutral_of_rowwiseNeutral
#print axioms Erdos287.AnchoredV3.exists_globalNeutral_not_rowwiseNeutral
#print axioms Erdos287.AnchoredV3.rowwise_sufficient_not_necessary
#print axioms Erdos287.AnchoredV3.exact_rowwise_subset_global
#print axioms Erdos287.AnchoredV3.modulus_eq_core_mul_mult

-- B. old-empty / new-hit certificate
#print axioms Erdos287.AnchoredV3.OldEmptyNewHit.newHit_reciprocal
#print axioms Erdos287.AnchoredV3.OldEmptyNewHit.newHit_exact
#print axioms Erdos287.AnchoredV3.OldEmptyNewHit.old_empty
#print axioms Erdos287.AnchoredV3.OldEmptyNewHit.same_bank_old_empty_new_global_hit

-- C. column zero patterns and the global column compiler
#print axioms Erdos287.AnchoredV3.sum_recip_zeroPattern
#print axioms Erdos287.AnchoredV3.Bank.delta_eq_of_neutral
#print axioms Erdos287.AnchoredV3.Bank.globalColumnCompiler
#print axioms Erdos287.AnchoredV3.Bank.globalColumnCompiler_baseline

-- D. column zero-sum packets
#print axioms Erdos287.AnchoredV3.ColumnPackets.exists_zeroSum_subset
#print axioms Erdos287.AnchoredV3.ColumnPackets.exists_zeroSum_subset_two_le
#print axioms Erdos287.AnchoredV3.ColumnPackets.exists_disjoint_packets
#print axioms Erdos287.AnchoredV3.ColumnPackets.sum_biUnion_eq_zero
#print axioms Erdos287.AnchoredV3.ColumnPackets.manyNeutralPackets_not_exactTarget

-- E. support size / multiplicity
#print axioms Erdos287.AnchoredV3.RowFibreData.card_fiber_le_prod
#print axioms Erdos287.AnchoredV3.RowFibreData.card_image_ge
#print axioms Erdos287.AnchoredV3.RowFibreData.uniformRowFibreBound_of_asymptotic

-- F. Boolean column gcd theorem
#print axioms Erdos287.AnchoredV3.ColumnLattice.coeff_gcd_dvd_patternWeights_gcd
#print axioms Erdos287.AnchoredV3.ColumnLattice.gcd_patternWeights_dvd_coeff
#print axioms Erdos287.AnchoredV3.ColumnLattice.boolean_column_gcd
#print axioms Erdos287.AnchoredV3.ColumnLattice.sharpness_witness_two

-- G. target mobility
#print axioms Erdos287.AnchoredV3.MobilityData.S_eq_num_div
#print axioms Erdos287.AnchoredV3.MobilityData.den_dvd_Dcore
#print axioms Erdos287.AnchoredV3.MobilityData.prime_dvd_den_imp_dvd_Dcore
#print axioms Erdos287.AnchoredV3.MobilityData.target_movement
#print axioms Erdos287.AnchoredV3.no00_preserved

-- H. distinctness and AP-free mobility
#print axioms Erdos287.AnchoredV3.MobilityFamily.W_injective_of_lt
#print axioms Erdos287.AnchoredV3.MobilityFamily.W_injective_boolean
#print axioms Erdos287.AnchoredV3.MobilityFamily.no_three_term_ap
#print axioms Erdos287.AnchoredV3.MobilityFamily.card_targets
#print axioms Erdos287.AnchoredV3.MobilityFamily.card_targets_add_targets
#print axioms Erdos287.AnchoredV3.MobilityFamily.gcd_cofactors_eq_one

-- I. combined alignment coefficient
#print axioms Erdos287.AnchoredV3.AlignedBank.target_moved
#print axioms Erdos287.AnchoredV3.AlignedBank.alignment_coefficient
#print axioms Erdos287.AnchoredV3.AlignedBank.alignment_sumset
#print axioms Erdos287.AnchoredV3.mobility_cofactor_gcd

-- J. Fourier / exponential tilt interface
#print axioms Erdos287.AnchoredV3.FiniteCoeff.Z_pos
#print axioms Erdos287.AnchoredV3.FiniteCoeff.sum_prob
#print axioms Erdos287.AnchoredV3.FiniteCoeff.norm_char_le_one
#print axioms Erdos287.AnchoredV3.coeff_pos_of_antiHoleBridge

-- K. baseline centrality
#print axioms Erdos287.AnchoredV3.mobility_cannot_repair_macroscopic_gap
#print axioms Erdos287.AnchoredV3.mobility_capacity_fraction

-- L. resonance interfaces
#print axioms Erdos287.AnchoredV3.Resonance.notMem_activeRows_iff
#print axioms Erdos287.AnchoredV3.Resonance.activeRows_private_prime
#print axioms Erdos287.AnchoredV3.Resonance.zero_phase_of_dvd
#print axioms Erdos287.AnchoredV3.Resonance.norm_columnProduct_le_one
#print axioms Erdos287.AnchoredV3.Resonance.norm_mobilityFactor_le_one
#print axioms Erdos287.AnchoredV3.Resonance.arc_bound_of_budgets

-- M. conditional terminal closure
#print axioms Erdos287.AnchoredV3.conditional_terminal_closure

end AnchoredV3
end Erdos287
