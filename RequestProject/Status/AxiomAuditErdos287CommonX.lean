import Mathlib
import RequestProject.Status.CurrentStatusErdos287CommonXFrontier

/-!
# Axiom audit — Erdős #287, COMMON-x / fractional-linear C0 Δ

`#print axioms` for every new declaration of this delta.

Allowed inherited axioms only:

```
propext, Classical.choice, Quot.sound
```

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `implemented_by` occurs as a
code construct in any module of this delta; the words appear only inside docstring prose.
Decidable ledger facts are discharged with `decide +kernel`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace CommonXAudit

/-! ## §2  Common-x conductor arithmetic -/

#print axioms Erdos287.CommonX.commonX_gcd
#print axioms Erdos287.CommonX.commonX_mul
#print axioms Erdos287.CommonX.commonX_lcm
#print axioms Erdos287.CommonX.commonX_gcd_coprime
#print axioms Erdos287.CommonX.commonX_lcm_coprime
#print axioms Erdos287.CommonX.commonX_dvd_left
#print axioms Erdos287.CommonX.commonX_dvd_right
#print axioms Erdos287.CommonX.commonX_dvd_gcd
#print axioms Erdos287.CommonX.commonX_gcd_mul_lcm

/-! ## §3  Centered `kappa` CRT arithmetic -/

#print axioms Erdos287.CommonX.kappa_crt_exists
#print axioms Erdos287.CommonX.kappa_mod_small
#print axioms Erdos287.CommonX.kappa_mod_long
#print axioms Erdos287.CommonX.kappa_unit_long
#print axioms Erdos287.CommonX.kappa_sub_one_coprime_long
#print axioms Erdos287.CommonX.kappa_sub_one_gcd_long_eq_one
#print axioms Erdos287.CommonX.gcd_kappa_sub_one_fullConductor
#print axioms Erdos287.CommonX.gcd_kappa_sub_one_fullConductor_of_crt

/-! ## §4  Centered graph-diagonal firewall -/

#print axioms Erdos287.CommonX.graph_diagonal_forces_full_gcd
#print axioms Erdos287.CommonX.gcd_eq_natAbs_of_dvd
#print axioms Erdos287.CommonX.graph_literal_diagonal_impossible
#print axioms Erdos287.CommonX.graph_diagonal_impossible_of_centered

/-! ## §7  Common-divisor collision firewall, and the x-row separation -/

#print axioms Erdos287.CommonX.commonDivisor_residue_compatible
#print axioms Erdos287.CommonX.commonDivisor_residue_cancel_unit
#print axioms Erdos287.CommonX.commonDivisor_residue_iff_unit
#print axioms Erdos287.CommonX.centered_kappa_satisfiable
#print axioms Erdos287.CommonX.xRowDiagonal_not_excluded

/-! ## §5–§6  Fractional-linear opposite-row algebra -/

#print axioms Erdos287.FractionalLinear.fractionalLinear_to_linear
#print axioms Erdos287.FractionalLinear.oppositeRow_linearized
#print axioms Erdos287.FractionalLinear.oppositeRow_unique_residue
#print axioms Erdos287.FractionalLinear.oppositeRow_unique_residue_of_source
#print axioms Erdos287.FractionalLinear.oppositeRow_unique_residue_zmod
#print axioms Erdos287.FractionalLinear.denominator_ne_zero_of_unit
#print axioms Erdos287.FractionalLinear.kappa_fractionalLinear_of_source
#print axioms Erdos287.FractionalLinear.kappa_fractionalLinear_of_source_zmod

/-! ## §11  Local change of variables (no Weil bound is claimed) -/

#print axioms Erdos287.FractionalLinear.affine_leftInverse
#print axioms Erdos287.FractionalLinear.affine_rightInverse
#print axioms Erdos287.FractionalLinear.affine_bijective
#print axioms Erdos287.FractionalLinear.affine_pole_iff
#print axioms Erdos287.FractionalLinear.sum_affine_reindex
#print axioms Erdos287.FractionalLinear.sum_affine_reindex_nonzero

/-! ## §8–§12  Status / ledger rows -/

#print axioms Erdos287.CommonXFrontierStatus.omegaNormalization_is_formal_first_residual
#print axioms Erdos287.CommonXFrontierStatus.doubleTypeII_is_research_first_analytic_residual
#print axioms Erdos287.CommonXFrontierStatus.c0_transverse_bdiagonal_all_reduced_open
#print axioms Erdos287.CommonXFrontierStatus.erdos287_open
#print axioms Erdos287.CommonXFrontierStatus.transverse_status_rows
#print axioms Erdos287.CommonXFrontierStatus.bdiagonal_status_rows
#print axioms Erdos287.CommonXFrontierStatus.typeI_typeII_rows_are_ledger_records
#print axioms Erdos287.CommonXFrontierStatus.typeI_closure_does_not_close_c0
#print axioms Erdos287.CommonXFrontierStatus.commonX_arithmetic_pass_does_not_imply_c0_closure
#print axioms
  Erdos287.CommonXFrontierStatus.fractionalLinear_pass_does_not_imply_kloosterman_estimate
#print axioms
  Erdos287.CommonXFrontierStatus.local_kloosterman_arithmetic_does_not_imply_spectral_closure
#print axioms Erdos287.CommonXFrontierStatus.no_false_promotions
#print axioms Erdos287.CommonXFrontierStatus.diagonal_ledger_rows
#print axioms Erdos287.CommonXFrontierStatus.status_does_not_encode_xRow_exclusion
#print axioms Erdos287.CommonXFrontierStatus.graphDiagonal_row_is_backed_by_a_theorem
#print axioms Erdos287.CommonXFrontierStatus.xRowDiagonal_row_is_backed_by_a_witness
#print axioms Erdos287.CommonXFrontierStatus.hybrid2_ledger_still_preserved
#print axioms Erdos287.CommonXFrontierStatus.caseB_ledger_still_preserved

end CommonXAudit
end Erdos287
