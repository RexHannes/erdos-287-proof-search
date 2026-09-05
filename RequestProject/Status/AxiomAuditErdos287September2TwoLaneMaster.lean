import RequestProject.Status.CurrentStatusErdos287September2TwoLaneMaster

/-!
# Axiom audit — the September-2 two-lane master source layer

This module is **append-only**.  It runs `#print axioms` on every principal declaration added
in this layer.  The expected output for each is the ordinary Mathlib set

```
[propext, Classical.choice, Quot.sound]
```

or a subset of it.  No custom `axiom`, no `sorryAx`, no `native_decide`, no `unsafe`, no
`opaque`, no `implemented_by` and no `debug.skipKernelTC` occurs in the new modules.
-/

namespace Erdos287
namespace September2TwoLaneMasterAxiomAudit

/-! ## Tagged two-lane source (§1–§2 of the bank) -/

#print axioms Erdos287.September2TaggedSource.lane_dichotomy
#print axioms Erdos287.September2TaggedSource.lanes_are_disjoint
#print axioms Erdos287.September2TaggedSource.census_union
#print axioms Erdos287.September2TaggedSource.census_disjoint
#print axioms Erdos287.September2TaggedSource.census_card_split
#print axioms Erdos287.September2TaggedSource.rawIndexEquiv
#print axioms Erdos287.September2TaggedSource.intendedTarget_injective
#print axioms Erdos287.September2TaggedSource.source_split_identity
#print axioms Erdos287.September2TaggedSource.tag_disjointness_is_not_support_disjointness
#print axioms Erdos287.September2TaggedSource.tot_rows_carry_no_selectedE
#print axioms Erdos287.September2TaggedSource.selectedE_isSome_iff_u
#print axioms Erdos287.September2TaggedSource.no_tot_constructor_carries_selectedE
#print axioms Erdos287.September2TaggedSource.selectedE_not_recoverable_from_tot_lane

/-! ## One-slot Perron kernel and finite ceilings (§4–§5) -/

#print axioms Erdos287.September2OneSlotPerron.height_div_abscissa
#print axioms Erdos287.September2OneSlotPerron.arsinh_gt_log_two_mul
#print axioms Erdos287.September2OneSlotPerron.arsinh_le_log_five_halves_mul
#print axioms Erdos287.September2OneSlotPerron.log_five_halves_pow_lt
#print axioms Erdos287.September2OneSlotPerron.perronMassOne_lt
#print axioms Erdos287.September2OneSlotPerron.eps_pos_lt_half
#print axioms Erdos287.September2OneSlotPerron.ceil_one_div_one_sub_gamma
#print axioms Erdos287.September2OneSlotPerron.coordCount_le_112
#print axioms Erdos287.September2OneSlotPerron.coordCount_max
#print axioms Erdos287.September2OneSlotPerron.nonempty_coordinate_subsets_card
#print axioms Erdos287.September2OneSlotPerron.enormous_bounds_are_not_effectivity

/-! ## Ledger pin, adapters, compilers, N2 and the four-error interface (§6–§13) -/

#print axioms Erdos287.September2Ledger.ledger_contract_is_a_genuine_constraint
#print axioms Erdos287.September2Ledger.ledger_contract_does_not_bound_the_mass
#print axioms Erdos287.September2Ledger.adapter_gives_componentwise_equality
#print axioms Erdos287.September2Ledger.selectedE_clause_cannot_be_dropped
#print axioms Erdos287.September2Ledger.bDiagonal_bypassed_conditionally
#print axioms Erdos287.September2Ledger.bypass_antecedent_is_not_asserted
#print axioms Erdos287.September2Ledger.E_L_conditional_bound
#print axioms Erdos287.September2Ledger.Cpair_C2LF_below_collar
#print axioms Erdos287.September2Ledger.fourLossSurvivalPositivity
#print axioms Erdos287.September2Ledger.PrimePairSieve.windowData_inhabited
#print axioms Erdos287.September2Ledger.PrimePairSieve.one_le_z
#print axioms Erdos287.September2Ledger.PrimePairSieve.z_lt_Q
#print axioms Erdos287.September2Ledger.PrimePairSieve.sector_element_exceeds_z
#print axioms Erdos287.September2Ledger.PrimePairSieve.two_le_sector_element
#print axioms Erdos287.September2Ledger.PrimePairSieve.shifted_element_exceeds_z
#print axioms Erdos287.September2Ledger.PrimePairSieve.no_small_prime_divisor
#print axioms Erdos287.September2Ledger.PrimePairSieve.primePairSieveSurvival45
#print axioms Erdos287.September2Ledger.PrimePairSieve.survival_bridge_is_not_the_analytic_sieve
#print axioms Erdos287.September2Ledger.two_XN2_exceeds_four_billion
#print axioms Erdos287.September2Ledger.fourErrorLowerBound
#print axioms Erdos287.September2Ledger.fourError_positivity_needs_all_four
#print axioms Erdos287.September2Ledger.fourError_budget_is_an_input

/-! ## The status layer (§14) -/

#print axioms Erdos287.September2TwoLaneMasterStatus.erdos287_is_open
#print axioms Erdos287.September2TwoLaneMasterStatus.no_status_row_closes_erdos287
#print axioms Erdos287.September2TwoLaneMasterStatus.open_and_conditional_rows_exist
#print axioms Erdos287.September2TwoLaneMasterStatus.twin_prime_is_not_a_node
#print axioms Erdos287.September2TwoLaneMasterStatus.oneSlotPerronMass_row_is_backed
#print axioms Erdos287.September2TwoLaneMasterStatus.finiteSourceCeilings_row_is_backed
#print axioms Erdos287.September2TwoLaneMasterStatus.taggedTwoLaneAlgebra_row_is_backed
#print axioms Erdos287.September2TwoLaneMasterStatus.primePairSurvivalBridge_row_is_backed
#print axioms Erdos287.September2TwoLaneMasterStatus.n2FiniteSplice_row_is_backed

end September2TwoLaneMasterAxiomAudit
end Erdos287
