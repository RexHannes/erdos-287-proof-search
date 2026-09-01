import RequestProject.Status.CurrentStatusErdos287RegularPerronSourceFrontier

/-!
# Axiom audit — regular-Perron source frontier layer

This module is **append-only**.  It runs `#print axioms` on every principal new
theorem of the layer.  The expected output for each is the ordinary Mathlib set

```
[propext, Classical.choice, Quot.sound]
```

or a subset of it.  No custom axiom, no `sorryAx`, no `native_decide`, no
`unsafe`, no `opaque` and no `implemented_by` occurs anywhere in the new
modules.
-/

namespace Erdos287
namespace RegularPerronAxiomAudit

/-! ## §1  K0-SP2 source object and partition -/

#print axioms Erdos287.K0SP2Source.sourceExpr_two_sign
#print axioms Erdos287.K0SP2Source.sectorExpr_union
#print axioms Erdos287.K0SP2Source.sourceExpr_four_sectors
#print axioms Erdos287.K0SP2Source.k0SP2_fourClass_partition_exact
#print axioms Erdos287.K0SP2Source.k0SP2_source_four_sector_reassembly

/-! ## §2  Repeated-Balanced7 finite arithmetic -/

#print axioms Erdos287.RepeatedBalanced7.moebius_prod_primes
#print axioms Erdos287.RepeatedBalanced7.depthMoebius_eq_subset_sum
#print axioms Erdos287.RepeatedBalanced7.depthMoebius_eq_alternating
#print axioms Erdos287.RepeatedBalanced7.depthMoebius_three_eq_Hrepeat
#print axioms Erdos287.RepeatedBalanced7.depthMoebius_three_eq_neg_choose
#print axioms Erdos287.RepeatedBalanced7.depthMoebius_three_table

/-! ## §3  Regular Perron parent and the reconstruction firewall -/

#print axioms Erdos287.RegularPerron.RegularPerronCoefficients.correlation_eq_filter
#print axioms Erdos287.RegularPerron.regularPerronInput_not_inhabited_here
#print axioms Erdos287.RegularPerron.perron_reconstruction_identity
#print axioms Erdos287.RegularPerron.perron_reconstruction_triangle
#print axioms Erdos287.RegularPerron.perron_reconstruction_not_inhabited_here

/-! ## §4  Template reassembly -/

#print axioms Erdos287.TemplateReassembly.TemplateFamily.template_correlation_reassembly
#print axioms Erdos287.TemplateReassembly.abs_sum_lt_sum_abs_counterexample
#print axioms Erdos287.TemplateReassembly.triangle_only_after_parent

/-! ## §5  Owner-scope and first-Cauchy firewalls -/

#print axioms Erdos287.OwnerScope.scope_separation
#print axioms Erdos287.OwnerScope.genericAdapter_uninhabited
#print axioms Erdos287.OwnerScope.same_shape_does_not_determine_row
#print axioms Erdos287.OwnerScope.shape_only_boxes_impossible
#print axioms Erdos287.FirstCauchy.sign_consumed_by_modulus
#print axioms Erdos287.FirstCauchy.cancellation_lost_after_cauchy

/-! ## §6  FCL error strength and the conditional bridge -/

#print axioms Erdos287.FCLErrorStrength.fixedRelativeSaving_not_arbitraryLogSaving
#print axioms Erdos287.FCLErrorStrength.finiteCompiler_consumes_only_fixed_relative_saving
#print axioms Erdos287.FCLWindowPair.windowPairSupply_of_positiveFCLMass
#print axioms Erdos287.FCLWindowPair.asymptotic_does_not_give_bounded_effective
#print axioms Erdos287.FCLWindowPair.effectiveWindowPairSupply_needs_uniform_witness

/-! ## §7  The status layer -/

#print axioms Erdos287.RegularPerronSourceFrontierStatus.regularPerronSourceFrontier_is_later
#print axioms Erdos287.RegularPerronSourceFrontierStatus.k0SP2_partition_row_is_kernel_proved
#print axioms
  Erdos287.RegularPerronSourceFrontierStatus.fclToWindowPair_row_is_kernel_proved_conditional
#print axioms Erdos287.RegularPerronSourceFrontierStatus.no_row_is_a_proof_claim

end RegularPerronAxiomAudit
end Erdos287
