import Mathlib
import RequestProject.Status.CurrentStatusErdos287Hybrid2Frontier

/-!
# Axiom audit — Erdős #287, HYBRID-2 / critical-rectangle Δ

`#print axioms` for every new principal declaration of this delta.

Allowed inherited axioms only:

```
propext, Classical.choice, Quot.sound
```

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `implemented_by` occurs in
any module of this delta.  Explicit theorem hypotheses (`hArch`, `hPacket`, `hLS`, `hArchB`,
`hPacketB`, `hLSB`, and the source gcd identities `h1`, `h2`) are **hypotheses**, not axioms:
they do not appear in any `#print axioms` output below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace Hybrid2Audit

/-! ## §3–§6  Unconditional arithmetic bank -/

#print axioms Erdos287.Hybrid2.mobius_opening_of_squarefree
#print axioms Erdos287.Hybrid2.mobius_opening_needs_squarefree
#print axioms Erdos287.Hybrid2.coprime_left_of_mul_coprime
#print axioms Erdos287.Hybrid2.coprime_right_of_mul_coprime
#print axioms Erdos287.Hybrid2.coprime_both_of_mul_coprime
#print axioms Erdos287.Hybrid2.isCoprime_both_of_mul_isCoprime
#print axioms Erdos287.Hybrid2.isCoprime_of_isInverseMod
#print axioms Erdos287.Hybrid2.reciprocal_cancel_common_factor
#print axioms Erdos287.Hybrid2.isCoprime_ell_of_inverse
#print axioms Erdos287.Hybrid2.baseConductor_gcd
#print axioms Erdos287.Hybrid2.fullConductor_gcd
#print axioms Erdos287.Hybrid2.fullConductor_needs_coprime
#print axioms Erdos287.Hybrid2.pairwise_factors_dvd
#print axioms Erdos287.Hybrid2.lcm_dvd_e
#print axioms Erdos287.Hybrid2.mul_eq_gcd_mul_lcm
#print axioms Erdos287.Hybrid2.g0_mul_g0prime_dvd_e_mul_difference
#print axioms Erdos287.Hybrid2.g0_mul_g0prime_does_not_divide_difference

/-! ## §7–§8  Analytic compiler (conditional) and harmonic summation (unconditional) -/

#print axioms Erdos287.Hybrid2.fixedEll_bound
#print axioms Erdos287.Hybrid2.sum_inv_Icc_le_one_add_log
#print axioms Erdos287.Hybrid2.ell_sum_harmonic
#print axioms Erdos287.Hybrid2.ell_sum_harmonic_two_min

/-! ## §9, §11, §12  `η` compiler and rectangle algebra -/

#print axioms Erdos287.Hybrid2.eta1
#print axioms Erdos287.Hybrid2.eta_sq_expand
#print axioms Erdos287.Hybrid2.eta1_nonneg
#print axioms Erdos287.Hybrid2.hybrid2_bound
#print axioms Erdos287.Hybrid2.rectangle_side1
#print axioms Erdos287.Hybrid2.rectangle_side2
#print axioms Erdos287.Hybrid2.rectangle_product
#print axioms Erdos287.Hybrid2.rectangle_intersection
#print axioms Erdos287.Hybrid2.topShell_e_lower_bound

/-! ## §10  Short-edge firewall -/

#print axioms Erdos287.Hybrid2.Hybrid2Survivor
#print axioms Erdos287.Hybrid2.ShortD
#print axioms Erdos287.Hybrid2.ShortM
#print axioms Erdos287.Hybrid2.ShortQ
#print axioms Erdos287.Hybrid2.LongEdgeRectangle
#print axioms Erdos287.Hybrid2.noncontraction_shortEdge_or_rectangle
#print axioms Erdos287.Hybrid2.hybrid2_survivor_union
#print axioms Erdos287.Hybrid2.rectangle_alone_does_not_capture_all_survivors
#print axioms Erdos287.Hybrid2.shortD_is_not_automatic

/-! ## §14  b-diagonal product-modulus bank -/

#print axioms Erdos287.BDiagonal.isCoprime_of_dvd_mul_sub_one
#print axioms Erdos287.BDiagonal.bdiag_crt_inverse_congr
#print axioms Erdos287.BDiagonal.bdiag_phase_product_modulus
#print axioms Erdos287.BDiagonal.bdiag_moebius_mul
#print axioms Erdos287.BDiagonal.bdiag_moebius_levelPair
#print axioms Erdos287.BDiagonal.bdiag_squarefree_split
#print axioms Erdos287.BDiagonal.reducedConductor
#print axioms Erdos287.BDiagonal.bdiag_reduced_conductor
#print axioms Erdos287.BDiagonal.bdiag_reduced_unit
#print axioms Erdos287.BDiagonal.bdiag_delta_contraction_conditional
#print axioms Erdos287.BDiagonal.bdiag_survivor_union

/-! ## §15  Frontier ledger -/

#print axioms Erdos287.Hybrid2FrontierStatus.stage
#print axioms Erdos287.Hybrid2FrontierStatus.hybrid2Ledger
#print axioms Erdos287.Hybrid2FrontierStatus.caseB_strictly_before_hybrid2_frontier
#print axioms Erdos287.Hybrid2FrontierStatus.primitiveFractionCritical_not_frontier
#print axioms Erdos287.Hybrid2FrontierStatus.omegaNormalization_is_formal_first_residual
#print axioms Erdos287.Hybrid2FrontierStatus.hybrid2_analytic_descendants_all_open
#print axioms Erdos287.Hybrid2FrontierStatus.hybrid2_longEdge_passedThrough_only_if_appropriate
#print axioms Erdos287.Hybrid2FrontierStatus.erdos287_open
#print axioms Erdos287.Hybrid2FrontierStatus.only_arithmetic_rows_are_unconditional
#print axioms Erdos287.Hybrid2FrontierStatus.hybrid2_survivor_union
#print axioms Erdos287.Hybrid2FrontierStatus.hybrid2_longEdge_pass_does_not_capture_survivors
#print axioms Erdos287.Hybrid2FrontierStatus.caseB_ledger_still_preserved
#print axioms Erdos287.Hybrid2FrontierStatus.primitiveFraction_ledger_still_preserved

end Hybrid2Audit
end Erdos287
