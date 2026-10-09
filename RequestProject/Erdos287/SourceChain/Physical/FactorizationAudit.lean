import RequestProject.Erdos287.SourceChain.Physical.TypeII.Constructed
import RequestProject.Erdos287.SourceChain.Physical.TypeII.HeathBrown

/-!
# Erdős #287 — Pascadi factorization / three-colour source: axiom audit

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Each line must report only `[propext, Classical.choice, Quot.sound]` (or a subset).
-/

/-! ### Pascadi Lemma 5.3 / Proposition 5.2 (constructive greedy proof) -/
#print axioms Erdos287.Physical.Factor.lemma53
#print axioms Erdos287.Physical.Factor.twoSlot
#print axioms Erdos287.Physical.Factor.prop52_additive
#print axioms Erdos287.Physical.Factor.prop52_real
#print axioms Erdos287.Physical.Factor.prop52_vector
#print axioms Erdos287.Physical.Factor.prop52_nat

/-! ### Structured support of the actual atoms -/
#print axioms Erdos287.Physical.Sieve.ScalarParams.kappa_sector
#print axioms Erdos287.Physical.Sieve.ScalarParams.boxVec_vecHyp
#print axioms Erdos287.Physical.Sieve.ScalarParams.boxVec_vecHyp_pascadi
#print axioms Erdos287.Physical.Sieve.ScalarParams.atomColour_spec
#print axioms Erdos287.Physical.Sieve.ScalarParams.atom_factorization
#print axioms Erdos287.Physical.Sieve.ScalarParams.atom_factorization_clean

/-! ### Three-colour tensorization -/
#print axioms Erdos287.Physical.Factor.card_compat_mul
#print axioms Erdos287.Physical.Sieve.ScalarParams.bcoef_tensor
#print axioms Erdos287.Physical.Sieve.ScalarParams.partCount_le
#print axioms Erdos287.Physical.Sieve.ScalarParams.colFactor_le_one
#print axioms Erdos287.Physical.Sieve.ScalarParams.colFactor_support
#print axioms Erdos287.Physical.Sieve.ScalarParams.abs_lowFactor_le
#print axioms Erdos287.Physical.Sieve.ScalarParams.lowFactor_support
#print axioms Erdos287.Physical.Sieve.ScalarParams.lowFactor_coprime_high
#print axioms Erdos287.Physical.Sieve.ScalarParams.colFactor_coprime
#print axioms Erdos287.Physical.Sieve.ScalarParams.ellX_tensor
#print axioms Erdos287.Physical.Sieve.ScalarParams.atomWeight_mul_le
#print axioms Erdos287.Physical.Sieve.ScalarParams.total_variation_le
#print axioms Erdos287.Physical.Sieve.ScalarParams.H_eq_of_T

/-! ### Constructed Type-II source (no split parameter) -/
#print axioms Erdos287.Physical.TypeII.physCoefAtom_reassemble
#print axioms Erdos287.Physical.TypeII.physCoefAtom_abs_le
#print axioms Erdos287.Physical.TypeII.physCoefAtom_coprime
#print axioms Erdos287.Physical.TypeII.physCoefAtom_ranges
#print axioms Erdos287.Physical.TypeII.abs_conv12_le
#print axioms Erdos287.Physical.TypeII.typeII_source_decomp
#print axioms Erdos287.Physical.TypeII.physOB_source_eq_T

/-! ### Heath–Brown sign (preserved) and its negative control -/
#print axioms Erdos287.Physical.TypeII.heathBrown
#print axioms Erdos287.Physical.TypeII.maynard_printed_sign_false
