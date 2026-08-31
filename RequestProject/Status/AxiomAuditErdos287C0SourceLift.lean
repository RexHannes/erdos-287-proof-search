import Mathlib
import RequestProject.Status.CurrentStatusErdos287C0SourceLift

/-!
# Axiom audit — Erdős #287, C0 source-lift Δ

`#print axioms` for every declaration of this delta.

Allowed inherited axioms only:

```
propext, Classical.choice, Quot.sound
```

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `implemented_by` occurs as
a code construct in any module of this delta; those words appear only inside docstring prose.
Decidable ledger facts are discharged with `decide +kernel`.

The conditional statements (`erdos287_C0_after_conditioned_transfer`,
`omegaH_energy_of_normalization`, `energy_transfer_of_depth_bound`,
`bprime_h0_global_energy_with_depth_bound`) depend only on their explicitly named hypotheses;
the two hypothesis shells are proved non-automatic, so nothing is silently discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace C0SourceLiftAudit

/-! ## §1  Primitive source forms (unconditional) -/

#print axioms Erdos287.SourceLift.SourceRow.erdos287_gamma1_primitive
#print axioms Erdos287.SourceLift.SourceRow.erdos287_gamma2_primitive
#print axioms Erdos287.SourceLift.SourceRow.erdos287_A0row_primitive
#print axioms Erdos287.SourceLift.SourceRow.erdos287_C0_primitive
#print axioms Erdos287.SourceLift.SourceRow.erdos287_u_pos
#print axioms Erdos287.SourceLift.SourceRow.erdos287_u'_pos
#print axioms Erdos287.SourceLift.SourceRow.erdos287_b_pos

/-! ## §2  Pre-completion row representative (unconditional) -/

#print axioms Erdos287.SourceLift.erdos287_Q2_dvd
#print axioms Erdos287.SourceLift.erdos287_A0pre_sub_A0row
#print axioms Erdos287.SourceLift.erdos287_A0pre_dvd_sub
#print axioms Erdos287.SourceLift.erdos287_A0pre_congr_A0row
#print axioms Erdos287.SourceLift.erdos287_A0pre_congr_A0row_row

/-! ## §3  Raw → reduced projective pair (unconditional) -/

#print axioms Erdos287.ReducedProjective.erdos287_F_pos
#print axioms Erdos287.ReducedProjective.erdos287_F_ne_zero
#print axioms Erdos287.ReducedProjective.erdos287_Praw_factor
#print axioms Erdos287.ReducedProjective.erdos287_Rraw_factor
#print axioms Erdos287.ReducedProjective.projective_collision_iff_of_row_factor
#print axioms Erdos287.ReducedProjective.erdos287_raw_projective_collision_iff_reduced
#print axioms Erdos287.ReducedProjective.projective_collision_invariant_under_row_scaling

/-! ## §4  `b'`-absorption and fixed depth (unconditional arithmetic record) -/

#print axioms Erdos287.ReducedProjective.erdos287_Pnat_slot_product
#print axioms Erdos287.ReducedProjective.erdos287_Rnat_slot_product
#print axioms Erdos287.ReducedProjective.erdos287_numerator_depth
#print axioms Erdos287.ReducedProjective.erdos287_denominator_depth
#print axioms Erdos287.ReducedProjective.erdos287_fixed_depth_exponent
#print axioms Erdos287.ReducedProjective.row_factors_may_differ

/-! ## §5  Generic `b'`/`ℓ₀'` product-fibre `L²` lemma (unconditional) -/

#print axioms Erdos287.BPrimeEnergy.product_fibre_l2_bound_of_fibre_card
#print axioms Erdos287.BPrimeEnergy.productFibre_card_le_of_second_mem
#print axioms Erdos287.BPrimeEnergy.product_fibre_l2_bound_of_second_cardinality
#print axioms Erdos287.BPrimeEnergy.bprime_h0_global_energy
#print axioms Erdos287.BPrimeEnergy.product_fibre_l2_bound_of_filtered
#print axioms Erdos287.BPrimeEnergy.bprime_h0_global_energy_congruence_filter

/-! ## §6  Conditional transfer statements (explicit hypotheses only) -/

#print axioms Erdos287.BPrimeEnergy.energy_transfer_of_depth_bound
#print axioms Erdos287.BPrimeEnergy.bprime_h0_global_energy_with_depth_bound
#print axioms Erdos287.ConditionedInverseConv.erdos287_C0_after_conditioned_transfer
#print axioms Erdos287.ConditionedInverseConv.omegaH_energy_of_normalization

/-! ## §7  Non-automaticity of the two open hypothesis shells -/

#print axioms Erdos287.ConditionedInverseConv.conditionedInverseConv_hypothesis_not_automatic
#print axioms Erdos287.ConditionedInverseConv.conditionedInverseConv_hypothesis_satisfiable
#print axioms Erdos287.ConditionedInverseConv.omegaH_normalization_not_automatic

/-! ## §8  Status ledger -/

#print axioms Erdos287.C0SourceLiftStatus.sourceLiftLedger
#print axioms Erdos287.C0SourceLiftStatus.banked_children_are_unconditional
#print axioms Erdos287.C0SourceLiftStatus.open_owners
#print axioms Erdos287.C0SourceLiftStatus.global_rows_not_closed
#print axioms Erdos287.C0SourceLiftStatus.no_analytic_row_is_banked
#print axioms Erdos287.C0SourceLiftStatus.depth_bound_not_formalised
#print axioms Erdos287.C0SourceLiftStatus.sourcelift_pass_does_not_imply_c0_closure
#print axioms Erdos287.C0SourceLiftStatus.commonX_ledger_still_preserved

end C0SourceLiftAudit
end Erdos287
