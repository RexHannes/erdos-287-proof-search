import RequestProject.Erdos287.SourceChain.Physical.TypeII.RemainingProviders
import RequestProject.Erdos287.SourceChain.Physical.TypeII.HeathBrown

/-!
# Erdős #287 — parameter / source-fit / Ordering-B junction: axiom audit

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Each line must report only `[propext, Classical.choice, Quot.sound]` (or a subset).  The
provider `def`s are `Prop`s (not axioms); the conditional theorem takes them as hypotheses.
-/

/-! ### Priority 1: actual parameters -/
#print axioms Erdos287.Physical.Sieve.ScalarParams.Dlow_eq_rpow_beta
#print axioms Erdos287.Physical.Sieve.ScalarParams.critRegime_Tchoice
#print axioms Erdos287.Physical.Sieve.ScalarParams.beta_lt_kappa
#print axioms Erdos287.Physical.Sieve.ScalarParams.Dlow_sq_le
#print axioms Erdos287.Physical.Sieve.ScalarParams.crit_N_lo
#print axioms Erdos287.Physical.Sieve.ScalarParams.crit_N_hi
#print axioms Erdos287.Physical.Sieve.ScalarParams.atomParams_of_crit
#print axioms Erdos287.Physical.Sieve.ScalarParams.atom_factorization_actual

/-! ### Priority 2: source-to-provider dictionary -/
#print axioms Erdos287.Physical.TypeII.boxed_one
#print axioms Erdos287.Physical.TypeII.boxed_two
#print axioms Erdos287.Physical.TypeII.boxed_three
#print axioms Erdos287.Physical.TypeII.boxed_mono
#print axioms Erdos287.Physical.TypeII.physCoefAtom_eq_dict
#print axioms Erdos287.Physical.TypeII.lowFactor_coprime_col
#print axioms Erdos287.Physical.TypeII.physAtom_provider_contract

/-! ### Priority 3: composed source theorems -/
#print axioms Erdos287.Physical.TypeII.sum_box_dyadic
#print axioms Erdos287.Physical.TypeII.scalarTypeII_eq_cells
#print axioms Erdos287.Physical.TypeII.packet_typeII_eq_cells
#print axioms Erdos287.Physical.TypeII.physCell_contract
#print axioms Erdos287.Physical.TypeII.physCell_T_eq_zero
#print axioms Erdos287.Physical.TypeII.scalarTypeII_bound_of_cells
#print axioms Erdos287.Physical.TypeII.scalarTypeII_bound_of_providers

/-! ### Preserved negative control (Heath–Brown printed sign) -/
#print axioms Erdos287.Physical.TypeII.maynard_printed_sign_false
