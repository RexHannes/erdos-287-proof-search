import RequestProject.Erdos287.AnchoredV4.OpenOwners

/-!
# Anchored V4 — axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Every principal exported theorem of the Anchored V4 layer is checked here with `#print axioms`.
No custom `axiom`, `sorry`, `admit`, `native_decide`, `unsafe`, `opaque` or `@[implemented_by]`
occurs anywhere in this layer; the only axioms reported are Lean's standard `propext`,
`Classical.choice` and `Quot.sound` (several theorems use fewer).  The `decide` calls used in the
finite witnesses are kernel-reducible and introduce no axiom dependency.
-/

namespace Erdos287
namespace AnchoredV4

-- A. normalized prime-power height and the doubled lattice
#print axioms Erdos287.AnchoredV4.prime_pow_dvd_L_iff
#print axioms Erdos287.AnchoredV4.normalizedHeight_le_iff_dvd_two_lcm
#print axioms Erdos287.AnchoredV4.two_factor_essential
#print axioms Erdos287.AnchoredV4.normalizedHeight_not_le_iff_dvd_lcm
#print axioms Erdos287.AnchoredV4.den_two_mul_dvd_iff
#print axioms Erdos287.AnchoredV4.den_two_mul_dvd_L_iff_normHeight
#print axioms Erdos287.AnchoredV4.doubled_lattice_regression
#print axioms Erdos287.AnchoredV4.den_dvd_not_iff_den_two_mul_dvd

-- B. guard geometry
#print axioms Erdos287.AnchoredV4.noAdjacent_of_all_even
#print axioms Erdos287.AnchoredV4.noAdjacent_insert_even_of_mask
#print axioms Erdos287.AnchoredV4.noAdjacent_union_even_of_mask
#print axioms Erdos287.AnchoredV4.wordSum_insert
#print axioms Erdos287.AnchoredV4.wordSum_erase
#print axioms Erdos287.AnchoredV4.wordSum_union

-- C. ENTRY
#print axioms Erdos287.AnchoredV4.Entry.height_gt
#print axioms Erdos287.AnchoredV4.Entry.noAdjacent_union_safe
#print axioms Erdos287.AnchoredV4.Entry.normHeight_den_init_le
#print axioms Erdos287.AnchoredV4.entryDegenerate

-- D. descent
#print axioms Erdos287.AnchoredV4.DescentStep.next_value
#print axioms Erdos287.AnchoredV4.DescentStep.next_component_lower
#print axioms Erdos287.AnchoredV4.descent_terminates
#print axioms Erdos287.AnchoredV4.descent_normHeight_le

-- E. guarded reservoir and the exact absorber
#print axioms Erdos287.AnchoredV4.GuardedReservoir.noAdjacent_absorb
#print axioms Erdos287.AnchoredV4.GuardedReservoir.wordSum_absorb
#print axioms Erdos287.AnchoredV4.positive_mass_not_exact_coverage
#print axioms Erdos287.AnchoredV4.exact_absorption_iff_weight_subsetSum
#print axioms Erdos287.AnchoredV4.exact_absorption_of_congruence
#print axioms Erdos287.AnchoredV4.fourier_count_identity
#print axioms Erdos287.AnchoredV4.congCount_pos_of_dominance
#print axioms Erdos287.AnchoredV4.exact_absorption_of_fourier_dominance

-- F. conditional exact endgame
#print axioms Erdos287.AnchoredV4.entry_to_low_height
#print axioms Erdos287.AnchoredV4.low_height_to_exact_absorb
#print axioms Erdos287.AnchoredV4.conditional_entry_to_exact_one

-- G. transition system, columns, mobility, obstructions
#print axioms Erdos287.AnchoredV4.den_dvd_quotient_iff
#print axioms Erdos287.AnchoredV4.descent_congruence_iff
#print axioms Erdos287.AnchoredV4.dvd_mul_iff_of_coprime
#print axioms Erdos287.AnchoredV4.TransitionSystem.solves_of_independent_repairs
#print axioms Erdos287.AnchoredV4.TransitionSystem.unsolvable_of_common_divisor
#print axioms Erdos287.AnchoredV4.gcdWitnessSystem_unsolvable
#print axioms Erdos287.AnchoredV4.descentStep_of_congruence
#print axioms Erdos287.AnchoredV4.coset_meets_subgroup_iff
#print axioms Erdos287.AnchoredV4.mobility_targets_not_hit
#print axioms Erdos287.AnchoredV4.normHeight_le_self
#print axioms Erdos287.AnchoredV4.Entry.Q_lt_mem
#print axioms Erdos287.AnchoredV4.noAdjacent_card_bound

-- H. reconciliation with the frozen V3 bank and the original-problem bridge
#print axioms Erdos287.AnchoredV4.mobility_preserves_doubled_lattice
#print axioms Erdos287.AnchoredV4.absorber_is_sumset_membership
#print axioms Erdos287.AnchoredV4.noAdjacent_to_V3_no00
#print axioms Erdos287.AnchoredV4.dvd_iff_forall_component
#print axioms Erdos287.AnchoredV4.v4_firewalls_in_force
#print axioms Erdos287.AnchoredV4.final_configuration_is_counterexample
#print axioms Erdos287.AnchoredV4.conditional_entry_gives_counterexample
#print axioms Erdos287.AnchoredV4.no_entry_supply_of_no_counterexample
#print axioms Erdos287.AnchoredV4.OpenOwners.entry_to_original_287_bridge
#print axioms Erdos287.AnchoredV4.OpenOwners.open_owners
#print axioms Erdos287.AnchoredV4.OpenOwners.false_shortcuts

end AnchoredV4
end Erdos287
