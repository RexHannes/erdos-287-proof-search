import Mathlib
import RequestProject.Status.CurrentStatusErdos287OneLevelMobius

/-!
# Axiom audit — Erdős #287, ONE-LEVEL MÖBIUS Δ

`#print axioms` for **every** new principal declaration of this delta (§§1–14).

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
namespace OneLevelMobiusAudit

/-! ## §§1–3, §5  Product-modulus compression, `gcd(D,n)=1`, divisor split, Farey kernel -/

#print axioms Erdos287.LevelPairProduct.moebius_levelPair_compress
#print axioms Erdos287.LevelPairProduct.moebius_levelPair_eq_moebius_n
#print axioms Erdos287.LevelPairProduct.lcm_levelPair_eq
#print axioms Erdos287.LevelPairProduct.gcd_D_n_eq_one
#print axioms Erdos287.LevelPairProduct.gcd_D_lambda_dvd_g0_reexport
#print axioms Erdos287.LevelPairProduct.unitary_split_coprime
#print axioms Erdos287.LevelPairProduct.unitary_split_dvd
#print axioms Erdos287.LevelPairProduct.levelPair_norm_eq
#print axioms Erdos287.LevelPairProduct.levelPair_divisorSplit
#print axioms Erdos287.LevelPairProduct.levelPair_reindex_fixed_n
#print axioms Erdos287.LevelPairProduct.levelPair_reindex
#print axioms Erdos287.LevelPairProduct.fareyDifference_eq_D_div_g0n
#print axioms Erdos287.LevelPairProduct.fareyDifference_split_invariant

/-! ## §4  Fixed-`D` frequency rigidity -/

#print axioms Erdos287.LevelPairRigidity.t1_congr_mod_r1
#print axioms Erdos287.LevelPairRigidity.t2_congr_mod_r2
#print axioms Erdos287.LevelPairRigidity.fixedD_solution_of_bezout
#print axioms Erdos287.LevelPairRigidity.fixedD_solution_iff
#print axioms Erdos287.LevelPairRigidity.fixedD_u_period_g0
#print axioms Erdos287.LevelPairRigidity.primitive_split_g0_r
#print axioms Erdos287.LevelPairRigidity.primitive_r_side_independent_of_u
#print axioms Erdos287.LevelPairRigidity.fixedD_primitive_reduces_to_g0_side

/-! ## §6  CRT reciprocal normal form -/

#print axioms Erdos287.LevelPairReciprocal.exists_crtBeta
#print axioms Erdos287.LevelPairReciprocal.gcd_eq_one_of_congr
#print axioms Erdos287.LevelPairReciprocal.gcd_two_g0_beta_eq_one
#print axioms Erdos287.LevelPairReciprocal.crtNumerator
#print axioms Erdos287.LevelPairReciprocal.crtNumerator_congr
#print axioms Erdos287.LevelPairReciprocal.crtNumerator_rat
#print axioms Erdos287.LevelPairReciprocal.reciprocal_phase_normalForm
#print axioms Erdos287.LevelPairReciprocal.reciprocal_normalForm_of_inverse
#print axioms Erdos287.LevelPairReciprocal.global_inverse_restricts

/-! ## §§7–8  Fixed-`n` prime assignment and the non-multiplicativity firewall -/

#print axioms Erdos287.LevelPairPrimeAssignment.unitary_split_injOn
#print axioms Erdos287.LevelPairPrimeAssignment.unitary_split_image
#print axioms Erdos287.LevelPairPrimeAssignment.fixed_n_two_state_product
#print axioms Erdos287.LevelPairPrimeAssignment.localFactorK
#print axioms Erdos287.LevelPairPrimeAssignment.coeffK
#print axioms Erdos287.LevelPairPrimeAssignment.localFactorK_not_multiplicative

/-! ## §§9–10  Shared-gcd projector, Gram-as-square, `λ_H` harmonic mass -/

#print axioms Erdos287.SharedGcdGram.lambdaH
#print axioms Erdos287.SharedGcdGram.sum_lambdaH_divisors
#print axioms Erdos287.SharedGcdGram.divisorSupport
#print axioms Erdos287.SharedGcdGram.levelSlice
#print axioms Erdos287.SharedGcdGram.cofactorSlice
#print axioms Erdos287.SharedGcdGram.gcd_divisors_eq_filter
#print axioms Erdos287.SharedGcdGram.omega_gcd_eq_indicator_sum
#print axioms Erdos287.SharedGcdGram.gramSharedGcd
#print axioms Erdos287.SharedGcdGram.slice_sum_eq_square
#print axioms Erdos287.SharedGcdGram.double_sum_indicator
#print axioms Erdos287.SharedGcdGram.gram_expand
#print axioms Erdos287.SharedGcdGram.sharedGcd_gram_square
#print axioms Erdos287.SharedGcdGram.moebius_split_clean_sector
#print axioms Erdos287.SharedGcdGram.levelSlice_sum_factor
#print axioms Erdos287.SharedGcdGram.norm_sq_moebius_div
#print axioms Erdos287.SharedGcdGram.sharedGcd_oneLevel_gram
#print axioms Erdos287.SharedGcdGram.abs_lambdaH_le
#print axioms Erdos287.SharedGcdGram.biUnion_divisorsAntidiagonal
#print axioms Erdos287.SharedGcdGram.lambdaH_harmonic_mass_le
#print axioms Erdos287.SharedGcdGram.omega_support_mass_le

/-! ## §12  Complete primitive-`t` Ramanujan firewall -/

#print axioms Erdos287.PrimitiveTFirewall.int_gcd_prime_eq_one
#print axioms Erdos287.PrimitiveTFirewall.ramanujan_prime_not_dvd
#print axioms Erdos287.PrimitiveTFirewall.ramanujan_prime_dvd
#print axioms Erdos287.PrimitiveTFirewall.moebius_mul_ramanujan_prime
#print axioms Erdos287.PrimitiveTFirewall.moebius_ramanujan_normalForm_reexport

/-! ## §§11, 13  The two uninhabited analytic sockets -/

#print axioms Erdos287.SharedGcdOneLevel.EnergyLedger
#print axioms Erdos287.SharedGcdOneLevel.EnergyLedger.subpolytopeMargin
#print axioms Erdos287.SharedGcdOneLevel.EnergyLedger.Valid
#print axioms Erdos287.SharedGcdOneLevel.exists_valid_energyLedger
#print axioms Erdos287.SharedGcdOneLevel.SharedGcdOneLevelEnergyInput
#print axioms Erdos287.SharedGcdOneLevel.sharedGcdOneLevelEnergy_compiler
#print axioms Erdos287.SharedGcdOneLevel.sharedGcdOneLevelEnergy_not_automatic
#print axioms Erdos287.SharedGcdOneLevel.OneLevelMobiusConfig
#print axioms Erdos287.SharedGcdOneLevel.OneLevelMobiusConfig.source
#print axioms Erdos287.SharedGcdOneLevel.OneLevelMobiusConfig.Valid
#print axioms Erdos287.SharedGcdOneLevel.exists_valid_config_with_positive_source
#print axioms Erdos287.SharedGcdOneLevel.SharedGcdOneLevelMobiusGramInput
#print axioms Erdos287.SharedGcdOneLevel.sharedGcdOneLevelMobiusGram_compiler
#print axioms Erdos287.SharedGcdOneLevel.sharedGcdOneLevelMobiusGram_not_automatic

/-! ## §14  The new append-only status ledger -/

#print axioms Erdos287.OneLevelMobiusStatus.ledger
#print axioms Erdos287.OneLevelMobiusStatus.residualRank
#print axioms Erdos287.OneLevelMobiusStatus.no_closed_rows
#print axioms Erdos287.OneLevelMobiusStatus.erdos287_open
#print axioms Erdos287.OneLevelMobiusStatus.uniform_k0_open_fcl_not_reached
#print axioms Erdos287.OneLevelMobiusStatus.amplitude_exponents
#print axioms Erdos287.OneLevelMobiusStatus.cauchyConfiguration_superseded_not_closed
#print axioms Erdos287.OneLevelMobiusStatus.largeSharedG0_retracted_and_nearFreq_open
#print axioms Erdos287.OneLevelMobiusStatus.energy_subpolytope_provisional_not_closed
#print axioms Erdos287.OneLevelMobiusStatus.oneLevelMobiusGram_is_first_exact_residual
#print axioms Erdos287.OneLevelMobiusStatus.signed_levelPair_gram_strictly_reduced
#print axioms Erdos287.OneLevelMobiusStatus.exact_rows_are_theorems
#print axioms Erdos287.OneLevelMobiusStatus.gram_square_and_one_level_are_theorems
#print axioms Erdos287.OneLevelMobiusStatus.nonmultiplicativity_firewall_is_explicit
#print axioms Erdos287.OneLevelMobiusStatus.historical_sharedG0_status_preserved

end OneLevelMobiusAudit
end Erdos287
