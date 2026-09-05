import RequestProject.Status.CurrentStatusErdos287September4SignedFloorBank

/-!
# Axiom audit — the September-4 signed `B_src` floor bank

This module is **append-only**.  It runs `#print axioms` on every principal declaration
added in this layer.  The expected output for each is the ordinary Mathlib set

```
[propext, Classical.choice, Quot.sound]
```

or a subset of it.  In the new modules there is no custom `axiom`, no `sorry` / `sorryAx`,
no `native_decide`, no `unsafe`, no `opaque`, no `implemented_by` and no
`debug.skipKernelTC`.  The two decimal facts of this layer — the exact rational budget
`poleBudget + oscillatoryBudget < 10⁻⁶` and the tail endpoint
`9360 · 62.5 · 63.5 · exp(−31.25) < 10⁻⁶` — are both discharged inside the kernel, the
latter from the Taylor bound `7889/6144 ≤ exp(1/4)` and the exact rational inequality
`37147500 · 10⁶ < (7889/6144)^125`.
-/

namespace Erdos287
namespace September4SignedFloorBankAxiomAudit

/-! ## §1  The physical weight `W` -/

#print axioms Erdos287.September4PhysicalW.W_support_subset
#print axioms Erdos287.September4PhysicalW.W_seven_tenths
#print axioms Erdos287.September4PhysicalW.W_nine_tenths
#print axioms Erdos287.September4PhysicalW.W_four_fifths
#print axioms Erdos287.September4PhysicalW.W_nonneg
#print axioms Erdos287.September4PhysicalW.W_le_one
#print axioms Erdos287.September4PhysicalW.W_strictMonoOn_left
#print axioms Erdos287.September4PhysicalW.W_strictAntiOn_right
#print axioms Erdos287.September4PhysicalW.W_isGreatest_one
#print axioms Erdos287.September4PhysicalW.W_sSup_range
#print axioms Erdos287.September4PhysicalW.W_iSup
#print axioms Erdos287.September4PhysicalW.W_variation_left
#print axioms Erdos287.September4PhysicalW.W_variation_right
#print axioms Erdos287.September4PhysicalW.W_variation_Icc
#print axioms Erdos287.September4PhysicalW.physicalW_variation
#print axioms Erdos287.September4PhysicalW.physicalW_CW_eq_four
#print axioms Erdos287.September4PhysicalW.W_hasDerivAt

/-! ## §2  Canonical-state sign invariance -/

#print axioms Erdos287.September4CanonicalStateSign.moebius_eq_neg_one_pow_omega
#print axioms Erdos287.September4CanonicalStateSign.canonicalStateSignInvariance45
#print axioms Erdos287.September4CanonicalStateSign.canonicalStateSign_product
#print axioms Erdos287.September4CanonicalStateSign.thresholdCrossing_sign_flip
#print axioms Erdos287.September4CanonicalStateSign.thresholdCrossing_sign_invariance

/-! ## §3  `T⁰ − T²` deep-even cancellation -/

#print axioms Erdos287.September4T0T2.two_mul_dvd_iff_even
#print axioms Erdos287.September4T0T2.same_physical_n
#print axioms Erdos287.September4T0T2.kappa_reindex
#print axioms Erdos287.September4T0T2.weight_reindex
#print axioms Erdos287.September4T0T2.Bsrc_even_collapse
#print axioms Erdos287.September4T0T2.evenPart_reindex
#print axioms Erdos287.September4T0T2.t0t2SourceDecomposition
#print axioms Erdos287.September4T0T2.deepTerm_cancel
#print axioms Erdos287.September4T0T2.t0t2DeepEvenCancellation45
#print axioms Erdos287.September4T0T2.deepEven_is_not_complete_closure

/-! ## §4  The interior local Möbius collapse -/

#print axioms Erdos287.September4BsrcCollapse.localFactorIdentity
#print axioms Erdos287.September4BsrcCollapse.moebius_prod_primes
#print axioms Erdos287.September4BsrcCollapse.cubeLocalMobiusCollapse
#print axioms Erdos287.September4BsrcCollapse.interiorLocalMobiusCollapse45
#print axioms Erdos287.September4BsrcCollapse.interiorCollapse_normalized
#print axioms Erdos287.September4BsrcCollapse.interiorCollapse_S2_mu
#print axioms Erdos287.September4BsrcCollapse.interiorCollapse_S2_mu_of_prime
#print axioms Erdos287.September4BsrcCollapse.abstractLocalNormalisation_S2_mu_form_fails

/-! ## §5  The boundary divisor lattice -/

#print axioms Erdos287.September4BoundaryLattice.interior_consumed
#print axioms Erdos287.September4BoundaryLattice.interior_or_boundary
#print axioms Erdos287.September4BoundaryLattice.collapse_fails_on_truncated_fibre
#print axioms Erdos287.September4BoundaryLattice.boundary_cause_list_card
#print axioms Erdos287.September4BoundaryLattice.exhaustiveness_is_relative

/-! ## §6–§7  The signed `B_src` compiler and the secondary-pole interface -/

#print axioms Erdos287.September4SignedCompiler.affineSigns_card
#print axioms Erdos287.September4SignedCompiler.factor_minus_four
#print axioms Erdos287.September4SignedCompiler.signedBsrcSourceIdentity45
#print axioms Erdos287.September4SignedCompiler.signedBsrcSourceIdentity45_expanded
#print axioms Erdos287.September4SignedCompiler.shoulder_of_residue_quarter
#print axioms Erdos287.September4SignedCompiler.shoulder_of_secondaryPoleInput

/-! ## §8–§10  The budget, the checker, and the conditional closures -/

#print axioms Erdos287.September4Checker.budget_sum_lt_target
#print axioms Erdos287.September4Checker.budget_values
#print axioms Erdos287.September4Checker.signedFloor_budget_compiler
#print axioms Erdos287.September4Checker.chainCovers_sound
#print axioms Erdos287.September4Checker.checker_coverage
#print axioms Erdos287.September4Checker.list_contrib_le_total
#print axioms Erdos287.September4Checker.boundaryCertificateChecker_sound
#print axioms Erdos287.September4Checker.boundaryCertificateValid_implies_compactSlab
#print axioms Erdos287.September4Checker.slab_and_tail_join
#print axioms Erdos287.September4Checker.no_banked_certificate
#print axioms Erdos287.September4Checker.structuralDemoCertificate_checks
#print axioms Erdos287.September4Checker.structuralDemoCertificate_has_no_classes

/-! ## §11  The large-`L` tail envelope -/

#print axioms Erdos287.September4LargeLTail.envelope_hasDerivAt
#print axioms Erdos287.September4LargeLTail.envelope_deriv_neg
#print axioms Erdos287.September4LargeLTail.envelope_strictAntiOn
#print axioms Erdos287.September4LargeLTail.exp_quarter_lower
#print axioms Erdos287.September4LargeLTail.exp_endpoint_lower
#print axioms Erdos287.September4LargeLTail.envelope_endpoint
#print axioms Erdos287.September4LargeLTail.largeL_tail_envelope_bound
#print axioms Erdos287.September4LargeLTail.largeL_tail_compiler

/-! ## §14  Status-layer firewalls and row backings -/

#print axioms Erdos287.September4SignedFloorBankStatus.deepEven_is_not_floor_closure
#print axioms Erdos287.September4SignedFloorBankStatus.checker_coexists_with_missing_certificate
#print axioms Erdos287.September4SignedFloorBankStatus.secondaryPole_is_external
#print axioms Erdos287.September4SignedFloorBankStatus.maynard_is_not_asserted
#print axioms Erdos287.September4SignedFloorBankStatus.mertens_is_not_asserted
#print axioms Erdos287.September4SignedFloorBankStatus.boundary_exhaustiveness_is_partial
#print axioms Erdos287.September4SignedFloorBankStatus.erdos287_remains_open
#print axioms
  Erdos287.September4SignedFloorBankStatus.source_algebra_does_not_upgrade_analytic_rows
#print axioms Erdos287.September4SignedFloorBankStatus.row_wSupport_backed
#print axioms Erdos287.September4SignedFloorBankStatus.row_wSupNorm_backed
#print axioms Erdos287.September4SignedFloorBankStatus.row_wVariation_backed
#print axioms Erdos287.September4SignedFloorBankStatus.row_cW4_backed
#print axioms Erdos287.September4SignedFloorBankStatus.row_canonicalStateSign_backed
#print axioms Erdos287.September4SignedFloorBankStatus.row_t0t2DeepEven_backed
#print axioms Erdos287.September4SignedFloorBankStatus.row_interiorMobiusCollapse_backed
#print axioms Erdos287.September4SignedFloorBankStatus.row_signedCompilerFinite_backed
#print axioms Erdos287.September4SignedFloorBankStatus.row_exactRationalBudget_backed
#print axioms Erdos287.September4SignedFloorBankStatus.row_boundaryChecker_backed
#print axioms Erdos287.September4SignedFloorBankStatus.row_boundaryNumericalCertificate_backed
#print axioms Erdos287.September4SignedFloorBankStatus.row_tailEnvelope_backed

end September4SignedFloorBankAxiomAudit
end Erdos287
