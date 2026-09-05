import RequestProject.Status.CurrentStatusErdos287September3SourceBank

/-!
# Axiom audit — the September-3 finite-chain / 2-adic source bank

This module is **append-only**.  It runs `#print axioms` on every principal declaration
added in this layer.  The expected output for each is the ordinary Mathlib set

```
[propext, Classical.choice, Quot.sound]
```

or a subset of it.  In the new modules there is no custom `axiom`, no `sorry` / `sorryAx`,
no `native_decide`, no `unsafe`, no `opaque`, no `implemented_by` and no
`debug.skipKernelTC`.  In particular the 24-window finite extension is replayed entirely by
kernel computation: every primality side condition is a recursive Pratt certificate whose
modular exponentiations are `decide`d on the *proved-correct* `Erdos287.Pratt.powMod`.
-/

namespace Erdos287
namespace September3SourceBankAxiomAudit

/-! ## The Pratt certificate engine -/

#print axioms Erdos287.Pratt.powMod_eq
#print axioms Erdos287.Pratt.exists_mem_of_prime_dvd
#print axioms Erdos287.Pratt.natCast_pow_eq_one_iff
#print axioms Erdos287.Pratt.prime_of_certificate

/-! ## Representative primality certificates (largest of each window family) -/

#print axioms Erdos287.Certificates.prime_1999999861
#print axioms Erdos287.Certificates.prime_8388607042343977
#print axioms Erdos287.Certificates.prime_16777214084687899
#print axioms Erdos287.Certificates.prime_33554428169375797

/-! ## The 24-window finite extension -/

#print axioms Erdos287.Gap2CE.windowStepExt_0
#print axioms Erdos287.Gap2CE.windowStepExt_23
#print axioms Erdos287.Gap2CE.no_of_M_le_extendedCeiling
#print axioms Erdos287.no_Erdos287Counterexample_of_max_le_extendedCeiling
#print axioms Erdos287.arithmeticCoverage_exceeds_twoExp375

/-! ## The 2-adic Möbius source pairing -/

#print axioms Erdos287.September3TwoAdicPairing.moebius_two_mul_odd
#print axioms Erdos287.September3TwoAdicPairing.odd_of_all_prime_factors_gt_two
#print axioms Erdos287.September3TwoAdicPairing.odd_mul_of_odd_odd
#print axioms Erdos287.September3TwoAdicPairing.sigmaEps_odd
#print axioms Erdos287.September3TwoAdicPairing.twoAdicMobiusPairCoefficient
#print axioms Erdos287.September3TwoAdicPairing.oddDivisorTotSourceIdentity
#print axioms Erdos287.September3TwoAdicPairing.oddDivisorTotSourceIdentity_filtered
#print axioms Erdos287.September3TwoAdicPairing.totLaneSourceSplit
#print axioms Erdos287.September3TwoAdicPairing.termwise_triangle_loses_pairing

/-! ## The odd-`d` / `4d` fixed-residue arithmetic -/

#print axioms Erdos287.September3FixedResidue.family0_fixedResidue
#print axioms Erdos287.September3FixedResidue.family0_fixedResidue_pm
#print axioms Erdos287.September3FixedResidue.isCoprime_two_of_odd
#print axioms Erdos287.September3FixedResidue.family0_integrality
#print axioms Erdos287.September3FixedResidue.family0_integrality_witness
#print axioms Erdos287.September3FixedResidue.family2_fixedResidue
#print axioms Erdos287.September3FixedResidue.family2_fixedResidue_pm
#print axioms Erdos287.September3FixedResidue.fixedResidueFamilies_replace_generic_modulus

/-! ## The conditional fixed-residue AP compiler -/

#print axioms Erdos287.September3ConditionalCompiler.PhysicalSlotFamily.slotIndex_card
#print axioms Erdos287.September3ConditionalCompiler.PhysicalSlotFamily.slotIndex_fiber_card
#print axioms Erdos287.September3ConditionalCompiler.abs_familySign
#print axioms Erdos287.September3ConditionalCompiler.totLaneFixedResidueConditionalBound45
#print axioms
  Erdos287.September3ConditionalCompiler.totLaneFixedResidueConditionalBound45_factored

/-! ## The canonical-split four-interval geometry -/

#print axioms Erdos287.September3CanonicalSplit.exists_threshold_of_monotone
#print axioms Erdos287.September3CanonicalSplit.monotone_rpow
#print axioms Erdos287.September3CanonicalSplit.canonicalSplit_two_thresholds
#print axioms Erdos287.September3CanonicalSplit.canonicalSplitFourInterval
#print axioms Erdos287.September3CanonicalSplit.canonicalSplit_upward_closed
#print axioms Erdos287.September3CanonicalSplit.crossing_at_half_exponent

/-! ## Status-layer firewalls and row backings -/

#print axioms Erdos287.September3SourceBankStatus.socket_is_not_kernelProved
#print axioms Erdos287.September3SourceBankStatus.finiteCoverage_does_not_close_medium_branch
#print axioms Erdos287.September3SourceBankStatus.conditionalCompiler_does_not_prove_erdos287
#print axioms Erdos287.September3SourceBankStatus.maynard_is_not_asserted
#print axioms Erdos287.September3SourceBankStatus.eT_and_eL_remain_conditional
#print axioms Erdos287.September3SourceBankStatus.row_finite24WindowExtension_backed
#print axioms Erdos287.September3SourceBankStatus.row_arithmeticCoverageEndpoint_backed
#print axioms Erdos287.September3SourceBankStatus.row_twoAdicMobiusPair_backed
#print axioms Erdos287.September3SourceBankStatus.row_fixedResidue_backed
#print axioms Erdos287.September3SourceBankStatus.row_conditionalCompiler_backed

end September3SourceBankAxiomAudit
end Erdos287
