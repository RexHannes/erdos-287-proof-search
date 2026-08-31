import Mathlib
import RequestProject.Status.CurrentStatusErdos287PrimitiveFractionCaseB

/-!
# Axiom audit — Erdős #287, CASE-B ONE-LEVEL PRIMITIVE-FRACTION Δ

`#print axioms` for every new principal declaration of this delta (§§2–11).

Allowed inherited axioms only:

```
propext, Classical.choice, Quot.sound
```

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `implemented_by` occurs in
any module of this delta.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace PrimitiveFractionCaseBAudit

/-! ## §2  Primitive-fraction spacing -/

#print axioms Erdos287.OneLevelSpacing.primitiveFraction_inj
#print axioms Erdos287.OneLevelSpacing.spacing_lower_bound
#print axioms Erdos287.OneLevelSpacing.spacing_uniform
#print axioms Erdos287.OneLevelSpacing.primitiveFraction_separation

/-! ## §4  Coefficient energy -/

#print axioms Erdos287.OneLevelEnergy.sum_inv_dyadic_le_one
#print axioms Erdos287.OneLevelEnergy.sum_inv_sq_dyadic_le
#print axioms Erdos287.OneLevelEnergy.coefficient_energy_bound

/-! ## §6  Projector `S1` / `S2` -/

#print axioms Erdos287.OneLevelProjector.sum_inv_sq_Icc_le
#print axioms Erdos287.OneLevelProjector.sum_inv_sq_Icc_le_two
#print axioms Erdos287.OneLevelProjector.sum_abs_moebius_div_le
#print axioms Erdos287.OneLevelProjector.lambdaH_S1_pair_le
#print axioms Erdos287.OneLevelProjector.projector_S1_bound
#print axioms Erdos287.OneLevelProjector.projector_S1_bound_real
#print axioms Erdos287.OneLevelProjector.projector_S2_bound

/-! ## §§3, 5  Weighted `d`-restricted large sieve and the fixed-`d` bound -/

#print axioms Erdos287.OneLevelWeightedLS.rho
#print axioms Erdos287.OneLevelWeightedLS.rho_nonneg
#print axioms Erdos287.OneLevelWeightedLS.rho_le
#print axioms Erdos287.OneLevelWeightedLS.weighted_sum_le_sup_mul
#print axioms Erdos287.OneLevelWeightedLS.largeSieve_separation_factor
#print axioms Erdos287.OneLevelWeightedLS.weighted_dRestricted_largeSieve
#print axioms Erdos287.OneLevelWeightedLS.fixedD_factor_identity
#print axioms Erdos287.OneLevelWeightedLS.fixedD_bound
#print axioms Erdos287.OneLevelWeightedLS.fixedD_bound_with_energy

/-! ## §§7–10  Global `Q_H`, normalised ratio, critical range -/

#print axioms Erdos287.OneLevelGlobal.global_QH_bound
#print axioms Erdos287.OneLevelGlobal.global_QH_envelope
#print axioms Erdos287.OneLevelGlobal.normalised_ratio_identity
#print axioms Erdos287.OneLevelGlobal.logPow_div_rpow_tendsto_zero
#print axioms Erdos287.OneLevelGlobal.logPow_div_le_of_polynomial_lower
#print axioms Erdos287.OneLevelGlobal.branch_G2_over_HX_closes
#print axioms Erdos287.OneLevelGlobal.branch_G_over_HA_closes
#print axioms Erdos287.OneLevelGlobal.critical_range_union

/-! ## §11  The new append-only status ledger -/

#print axioms Erdos287.PrimitiveFractionCaseBStatus.ledger
#print axioms Erdos287.PrimitiveFractionCaseBStatus.residualRank
#print axioms Erdos287.PrimitiveFractionCaseBStatus.no_closed_rows
#print axioms Erdos287.PrimitiveFractionCaseBStatus.erdos287_open
#print axioms Erdos287.PrimitiveFractionCaseBStatus.uniform_k0_open_fcl_not_reached
#print axioms Erdos287.PrimitiveFractionCaseBStatus.source_pins_unresolved
#print axioms
  Erdos287.PrimitiveFractionCaseBStatus.primitiveFractionCritical_is_first_exact_residual
#print axioms Erdos287.PrimitiveFractionCaseBStatus.spacing_row_is_a_theorem
#print axioms Erdos287.PrimitiveFractionCaseBStatus.largeSieve_row_is_a_theorem
#print axioms Erdos287.PrimitiveFractionCaseBStatus.coefficientEnergy_row_is_a_theorem
#print axioms Erdos287.PrimitiveFractionCaseBStatus.projector_row_is_a_theorem
#print axioms Erdos287.PrimitiveFractionCaseBStatus.global_row_is_a_theorem
#print axioms Erdos287.PrimitiveFractionCaseBStatus.normalisedRatio_row_is_a_theorem
#print axioms Erdos287.PrimitiveFractionCaseBStatus.small_parameter_rows_are_conditional
#print axioms Erdos287.PrimitiveFractionCaseBStatus.historical_status_preserved

end PrimitiveFractionCaseBAudit
end Erdos287
