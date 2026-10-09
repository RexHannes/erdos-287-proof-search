import RequestProject.Erdos287.ResearchBankV7.Ledger
import RequestProject.Erdos287.ResearchBankV7.V6Audit

/-!
# Research Bank V7 — axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Every principal V7 kernel theorem is audited here with `#print axioms`.  Only Lean's standard
`propext`, `Classical.choice` and `Quot.sound` may appear.

There is no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque` or `@[implemented_by]`
anywhere in the V7 layer.  The only computational steps are finite executable diagnostics
(`decide` on explicit finite data: the `J = L₄₄₇` size certificates, the audit fixtures and the
decidable ledger checks); they are kernel-reducible and are kept in their own declarations,
separate from the general mathematical theorems.
-/

namespace Erdos287
namespace ResearchBankV7

-- A.  Epochs and meta-firewalls
#print axioms Erdos287.ResearchBankV7.Epochs.epoch_index_injective
#print axioms Erdos287.ResearchBankV7.Epochs.superseded_does_not_mean_false
#print axioms Erdos287.ResearchBankV7.Epochs.superseded_flag_is_truth_neutral
#print axioms Erdos287.ResearchBankV7.Epochs.historical_open_does_not_determine_current_owner
#print axioms Erdos287.ResearchBankV7.Epochs.later_reduction_does_not_inhabit_earlier_owner
#print axioms Erdos287.ResearchBankV7.Epochs.no_closure_propagation_through_ledger_edges

-- B.  Bounded adaptive absorption
#print axioms Erdos287.ResearchBankV7.Absorption.card_le_of_fibre_bound
#print axioms Erdos287.ResearchBankV7.Absorption.guarded_charging
#print axioms Erdos287.ResearchBankV7.Absorption.unguarded_charging
#print axioms Erdos287.ResearchBankV7.Absorption.guarded_W_bound
#print axioms Erdos287.ResearchBankV7.Absorption.guarded_U_bound
#print axioms Erdos287.ResearchBankV7.Absorption.unguarded_W_bound
#print axioms Erdos287.ResearchBankV7.Absorption.unguarded_U_bound
#print axioms Erdos287.ResearchBankV7.Absorption.branching_bits_le
#print axioms Erdos287.ResearchBankV7.Absorption.charging_does_not_give_existence

-- C.  Exact interval lifting
#print axioms Erdos287.ResearchBankV7.IntervalLifting.interval_lift
#print axioms Erdos287.ResearchBankV7.IntervalLifting.lift_interval_nonempty
#print axioms Erdos287.ResearchBankV7.IntervalLifting.chain_reaches
#print axioms Erdos287.ResearchBankV7.IntervalLifting.chainSupport_card_le
#print axioms Erdos287.ResearchBankV7.IntervalLifting.chain_mass_eq
#print axioms Erdos287.ResearchBankV7.IntervalLifting.lift_failure_is_not_unsat

-- D.  Arithmetic spine
#print axioms Erdos287.ResearchBankV7.Spine.chainSupport_subset
#print axioms Erdos287.ResearchBankV7.Spine.SpineCert.spine_subset
#print axioms Erdos287.ResearchBankV7.Spine.SpineCert.spine_reaches
#print axioms Erdos287.ResearchBankV7.Spine.SpineCert.spine_reaches_all
#print axioms Erdos287.ResearchBankV7.Spine.SpineCert.spine_card_le
#print axioms Erdos287.ResearchBankV7.Spine.SpineCert.spine_mass_eq
#print axioms Erdos287.ResearchBankV7.Spine.spine_existence_not_claimed

-- E.  ERASURE-HIT
#print axioms Erdos287.ResearchBankV7.ErasureHit.erasure_hit
#print axioms Erdos287.ResearchBankV7.ErasureHit.erasure_hit_with_fixed_part
#print axioms Erdos287.ResearchBankV7.ErasureHit.erasure_hit_complement
#print axioms Erdos287.ResearchBankV7.ErasureHit.erasure_hit_rational

-- F.  Guarded branch-to-HIT
#print axioms Erdos287.ResearchBankV7.GuardedBranchHit.mass_eq_weight_div
#print axioms Erdos287.ResearchBankV7.GuardedBranchHit.GuardedBranch.deficit_eq
#print axioms Erdos287.ResearchBankV7.GuardedBranchHit.GuardedBranch.guarded_branch_to_hit
#print axioms Erdos287.ResearchBankV7.GuardedBranchHit.GuardedBranch.guards_preserved
#print axioms Erdos287.ResearchBankV7.GuardedBranchHit.guarded_hit_does_not_give_entry_word
#print axioms Erdos287.ResearchBankV7.GuardedBranchHit.guard_failure_does_not_kill_unguarded_branches
#print axioms Erdos287.ResearchBankV7.GuardedBranchHit.seed_mass_is_not_reference_mass

-- G.  Fixed-polylog completion: the finite components and the conditional theorem
#print axioms Erdos287.ResearchBankV7.PolylogCompletion.finite_second_moment
#print axioms Erdos287.ResearchBankV7.PolylogCompletion.buffer_packing
#print axioms Erdos287.ResearchBankV7.PolylogCompletion.polylog_completion_conditional
#print axioms Erdos287.ResearchBankV7.PolylogCompletion.conditional_does_not_inhabit_conclusion

-- H.  STABLE-ENTRY
#print axioms Erdos287.ResearchBankV7.StableEntry.AbsorptionSetup.stableEntry_forward
#print axioms Erdos287.ResearchBankV7.StableEntry.AbsorptionSetup.stableEntry_reverse
#print axioms Erdos287.ResearchBankV7.StableEntry.AbsorptionSetup.stableEntry_equivalence
#print axioms Erdos287.ResearchBankV7.StableEntry.stableEntry_equivalence_conditional
#print axioms Erdos287.ResearchBankV7.StableEntry.stableEntry_does_not_give_legal_seed
#print axioms Erdos287.ResearchBankV7.StableEntry.bounded_branching_does_not_decide_existence

-- I.  Fouvry pin localization (conditional records and finite consequences)
#print axioms Erdos287.ResearchBankV7.FouvryPin.pin_capture_conditional
#print axioms Erdos287.ResearchBankV7.FouvryPin.short_cofactor_pin_bound
#print axioms Erdos287.ResearchBankV7.FouvryPin.sublinear_support_cannot_capture_positive_proportion
#print axioms Erdos287.ResearchBankV7.FouvryPin.branch_budget_pin_localization
#print axioms Erdos287.ResearchBankV7.FouvryPin.fouvry_bound_does_not_give_terminal_leaf

-- J.  Finite source kills (finite executable diagnostics, kept separate)
#print axioms Erdos287.ResearchBankV7.FiniteSourceKills.sourceKill_2q_add_one
#print axioms Erdos287.ResearchBankV7.FiniteSourceKills.sourceKill_2q_sub_one
#print axioms Erdos287.ResearchBankV7.FiniteSourceKills.sourceKill_59
#print axioms Erdos287.ResearchBankV7.FiniteSourceKills.sourceKill_61
#print axioms Erdos287.ResearchBankV7.FiniteSourceKills.kill_pattern_not_universal
#print axioms Erdos287.ResearchBankV7.FiniteSourceKills.finite_kill_does_not_give_uniform_supply

-- K.  Numerical metadata (finite certificates)
#print axioms Erdos287.ResearchBankV7.Numerics.lcmRange_eq_lcmUpto
#print axioms Erdos287.ResearchBankV7.Numerics.J_decimal_bounds
#print axioms Erdos287.ResearchBankV7.Numerics.J_binary_bounds
#print axioms Erdos287.ResearchBankV7.Numerics.J_digits
#print axioms Erdos287.ResearchBankV7.Numerics.J_bits
#print axioms Erdos287.ResearchBankV7.Numerics.J_is_not_194_bits

-- L.  V6 spot audit
#print axioms Erdos287.ResearchBankV7.V6Audit.audit_actual_cofactors_denominator_entry
#print axioms Erdos287.ResearchBankV7.V6Audit.audit_actual_cofactors_carry
#print axioms Erdos287.ResearchBankV7.V6Audit.audit_actual_cofactors_aggregation
#print axioms Erdos287.ResearchBankV7.V6Audit.audit_selection_is_genuine
#print axioms Erdos287.ResearchBankV7.V6Audit.audit_no_hidden_conclusion_denominator_entry
#print axioms Erdos287.ResearchBankV7.V6Audit.audit_carry_premise_load_bearing
#print axioms Erdos287.ResearchBankV7.V6Audit.audit_support_disjointness_is_sharp

-- M.  Owners, DAG and ledger
#print axioms Erdos287.ResearchBankV7.Owners.upperGapCarryCompression_not_declared_false
#print axioms Erdos287.ResearchBankV7.Owners.exactMassIntersection_not_declared_false
#print axioms Erdos287.ResearchBankV7.Owners.exactMass_ready_given_entry
#print axioms Erdos287.ResearchBankV7.Owners.owner_kill_side_is_global
#print axioms Erdos287.ResearchBankV7.Owners.entry_node_specification_is_load_bearing
#print axioms Erdos287.ResearchBankV7.Owners.no_bypass_of_entry_node
#print axioms Erdos287.ResearchBankV7.Owners.dag_does_not_close
#print axioms Erdos287.ResearchBankV7.Ledger.ofV6_injective
#print axioms Erdos287.ResearchBankV7.Ledger.v6_classifications_preserved
#print axioms Erdos287.ResearchBankV7.Ledger.no_closed_verdict
#print axioms Erdos287.ResearchBankV7.Ledger.erdos287_ownerOpen
#print axioms Erdos287.ResearchBankV7.Ledger.entryOwner_ownerOpen
#print axioms Erdos287.ResearchBankV7.Ledger.external_rows_never_kernel

end ResearchBankV7
end Erdos287
