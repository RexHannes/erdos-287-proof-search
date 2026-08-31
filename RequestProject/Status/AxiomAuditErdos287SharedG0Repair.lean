import Mathlib
import RequestProject.Status.CurrentStatusErdos287SharedG0Repair

/-!
# Axiom audit — Erdős #287, SHARED-`g₀` CAUCHY REPAIR Δ

`#print axioms` for **every** new principal declaration of this delta (§§1–7, §9, §12).

Allowed inherited axioms only:

```
propext, Classical.choice, Quot.sound
```

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `implemented_by` occurs in
any module of this delta.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace SharedG0RepairAudit

/-! ## §1  Local-profile harmonic twists — `DET1-LOCALPROFILE-HARMONIC-TWISTS45` -/

#print axioms Erdos287.LocalProfileHarmonic.rad_ne_zero
#print axioms Erdos287.LocalProfileHarmonic.rad_squarefree
#print axioms Erdos287.LocalProfileHarmonic.gcd_rad_eq_one_iff
#print axioms Erdos287.LocalProfileHarmonic.squarefree_of_dvd_rad
#print axioms Erdos287.LocalProfileHarmonic.moebius_coprime_twist_sum
#print axioms Erdos287.LocalProfileHarmonic.twistInner_reindex
#print axioms Erdos287.LocalProfileHarmonic.mProfile_harmonic_twist_expansion

/-! ## §2  Fixed-`D` shared-`g₀` `u`-parametrisation — `DET1-SHAREDG0-PRIMITIVE-U-PARAM45` -/

#print axioms Erdos287.SharedG0Param.sharedG0_u_param_iff
#print axioms Erdos287.SharedG0Param.sharedG0_u_period
#print axioms Erdos287.SharedG0Param.primitive_not_dvd_t1
#print axioms Erdos287.SharedG0Param.primitive_not_dvd_t2
#print axioms Erdos287.SharedG0Param.excludedU_mem_iff
#print axioms Erdos287.SharedG0Param.excludedU_eq_iff_dvd_D
#print axioms Erdos287.SharedG0Param.card_excludedU

/-! ## §3  Shared-`g₀` local product — `DET1-SHAREDG0-PRIMITIVE-U-ROUTER45` -/

#print axioms Erdos287.SharedG0Router.norm_phase
#print axioms Erdos287.SharedG0Router.primitiveUSum_eq_complete_sub_excluded
#print axioms Erdos287.SharedG0Router.norm_primitiveUSum_le_modulus
#print axioms Erdos287.SharedG0Router.card_excludedResidues_le_two
#print axioms Erdos287.SharedG0Router.norm_primitiveUSum_le_two
#print axioms Erdos287.SharedG0Router.prod_primeFactors_dvd_gcd
#print axioms Erdos287.SharedG0Router.abs_prod_local_le
#print axioms Erdos287.SharedG0Router.phase_add
#print axioms Erdos287.SharedG0Router.admissible_mul_iff
#print axioms Erdos287.SharedG0Router.phase_crt_split
#print axioms Erdos287.SharedG0Router.primitiveUSum_crt_split

/-! ## §4  Unit-sector gcd reduction -/

#print axioms Erdos287.SharedG0UnitSector.gcd_congr_of_dvd_sub
#print axioms Erdos287.SharedG0UnitSector.gcd_unit_cancel
#print axioms Erdos287.SharedG0UnitSector.gcd_sub_comm
#print axioms Erdos287.SharedG0UnitSector.isCoprime_of_inverse
#print axioms Erdos287.SharedG0UnitSector.unitSector_coprime_of_inverses
#print axioms Erdos287.SharedG0UnitSector.sharedGcd_reciprocalDiff_eq_originalDiff
#print axioms Erdos287.SharedG0UnitSector.sharedGcd_unitTwisted_reciprocalDiff

/-! ## §5  Averaged `b`-pair gcd router — `DET1-SHAREDG0-BPAIR-AVERAGED45` -/

#print axioms Erdos287.SharedG0BPair.gcd_eq_sum_totient_divisors
#print axioms Erdos287.SharedG0BPair.int_gcd_eq_sum_totient_divisors
#print axioms Erdos287.SharedG0BPair.pairCountCongruentModulo_le
#print axioms Erdos287.SharedG0BPair.bpair_gcd_sum_le_divisorCount

/-! ## §6  Reduced denominator — `DET1-PRIMITIVE-REDUCED-DENOMINATOR45` -/

#print axioms Erdos287.ReducedDenominator.lcm_sharedG0_eq
#print axioms Erdos287.ReducedDenominator.gcd_D_lambda_coprime_left
#print axioms Erdos287.ReducedDenominator.gcd_D_lambda_coprime_right
#print axioms Erdos287.ReducedDenominator.gcd_D_lambda_dvd_g0
#print axioms Erdos287.ReducedDenominator.reducedDenominator_eq
#print axioms Erdos287.ReducedDenominator.reducedDenominator_ge

/-! ## §7  Near-frequency count precursor — `DET1-PRIMITIVE-NEARFREQ-COUNT45` -/

#print axioms Erdos287.NearFreqCount.g0_mul_lambda_eq
#print axioms Erdos287.NearFreqCount.nearFreqSet_eq
#print axioms Erdos287.NearFreqCount.nearFreq_D_mem_Icc
#print axioms Erdos287.NearFreqCount.nearFreqSet_card_le

/-! ## §9  The Cauchy-configuration repair socket — uninhabited -/

#print axioms Erdos287.SharedG0Cauchy.rootExponent_one
#print axioms Erdos287.SharedG0Cauchy.rootExponent_two
#print axioms Erdos287.SharedG0Cauchy.amplitude_dichotomy_nontrivial
#print axioms Erdos287.SharedG0Cauchy.exists_valid_ledger
#print axioms Erdos287.SharedG0Cauchy.sharedG0CauchyConfiguration_compiler
#print axioms Erdos287.SharedG0Cauchy.sharedG0CauchyConfiguration_not_automatic

/-! ## §12  The new status ledger -/

#print axioms Erdos287.SharedG0RepairStatus.no_closed_rows
#print axioms Erdos287.SharedG0RepairStatus.erdos287_open
#print axioms Erdos287.SharedG0RepairStatus.uniform_k0_open_fcl_not_reached
#print axioms Erdos287.SharedG0RepairStatus.two_analytic_children_repair_pending
#print axioms Erdos287.SharedG0RepairStatus.localProfileGram_strictly_reduced_not_promoted
#print axioms Erdos287.SharedG0RepairStatus.hardDen_child_conditional_not_promoted
#print axioms Erdos287.SharedG0RepairStatus.cauchyConfiguration_is_first_exact_research_residual
#print axioms Erdos287.SharedG0RepairStatus.exact_algebraic_rows_are_theorems
#print axioms Erdos287.SharedG0RepairStatus.router_crt_and_product_bound
#print axioms Erdos287.SharedG0RepairStatus.analytic_rows_are_uninhabited
#print axioms Erdos287.SharedG0RepairStatus.cauchy_amplitude_dichotomy_is_open
#print axioms Erdos287.SharedG0RepairStatus.historical_localProfile_status_preserved

end SharedG0RepairAudit
end Erdos287
