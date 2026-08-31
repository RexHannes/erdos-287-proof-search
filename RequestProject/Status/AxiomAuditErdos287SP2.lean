import Mathlib
import RequestProject.Status.Erdos287SP2Status

/-!
# SP-2 axiom audit

`#print axioms` for every principal SP-2 declaration.  Only `propext`, `Classical.choice`
and `Quot.sound` may appear.  No external analytic theorem enters through a user axiom,
and no SP-2 file contains `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`
or `@[implemented_by]`.
-/

-- Direct source adapter and the fixed certificate
#print axioms Erdos287.SP2Source.sp2_packet_metadata_inhabited
#print axioms Erdos287.SP2Source.sp2_fixedCertificate_divisorSum
#print axioms Erdos287.SP2Source.sp2_threeSeventh_lt_half
#print axioms Erdos287.SP2Source.sp2_half_lt_fourSeventh
#print axioms Erdos287.SP2Source.balancedSeven_threeFactor_below_cutoff
#print axioms Erdos287.SP2Source.balancedSeven_fourFactor_above_cutoff
#print axioms Erdos287.SP2Source.sp2_balancedSeven_subsetSizes
#print axioms Erdos287.SP2Source.sp2_balancedSeven_coefficient_eq_neg20
#print axioms Erdos287.SP2Source.sp2_divisorLattice_split

-- Literal prime-box weights
#print axioms Erdos287.SP2PrimeBox.sp2Omega_norm_le_one
#print axioms Erdos287.SP2PrimeBox.sp2Omega_eq_zero_of_not_mem
#print axioms Erdos287.SP2PrimeBox.sp2Omega_eq_one_of_mem
#print axioms Erdos287.SP2PrimeBox.sp2Omega_l1_eq_card
#print axioms Erdos287.SP2PrimeBox.sp2Adapter_pointwise
#print axioms Erdos287.SP2PrimeBox.sp2Adapter_prime_support
#print axioms Erdos287.SP2PrimeBox.sp2Adapter_not_automatic
#print axioms Erdos287.SP2PrimeBox.sp2_primeBoxL1_of_adapter
#print axioms Erdos287.SP2PrimeBox.sp2_outerInner_disjoint
#print axioms Erdos287.SP2PrimeBox.sp2_outerInner_cover
#print axioms Erdos287.SP2PrimeBox.sp2_no_primeDensity_doubleSpend
#print axioms Erdos287.SP2PrimeBox.sp2_block_cardinalities

-- Closure compiler
#print axioms Erdos287.SP2Closure.sp2_cutoff_eq_log
#print axioms Erdos287.SP2Closure.sp2_cvar_eq_five
#print axioms Erdos287.SP2Closure.sp2PhysicalLogPrefactor_not_automatic
#print axioms Erdos287.SP2Closure.sp2_netLogExponent_eq_neg_seven_halves
#print axioms Erdos287.SP2Closure.sp2_netLogExponent_lt_neg_one
#print axioms Erdos287.SP2Closure.sp2_closure_margin
#print axioms Erdos287.SP2Closure.sp2_closure_fails_without_audit
#print axioms Erdos287.SP2Closure.sp2_closes_logVar
#print axioms Erdos287.SP2Closure.sp2_supplies_primeBoxL1
#print axioms Erdos287.SP2Closure.balancedSeven_of_SP2_analytic_and_comparison
#print axioms Erdos287.SP2Closure.sp2_adapter_is_independent_of_ford723
#print axioms Erdos287.SP2Closure.sp2Closure_not_automatic
#print axioms Erdos287.SP2Closure.sp2Closure_cannot_construct_comparison
#print axioms Erdos287.SP2Closure.sp2_does_not_prove_balancedSeven

-- SP-2 status ledger
#print axioms Erdos287.SP2Status.fm723_adapter_retracted
#print axioms Erdos287.SP2Status.sp2_direct_adapter_controlling
#print axioms Erdos287.SP2Status.sp2_proved_layer
#print axioms Erdos287.SP2Status.sp2_first_exact_residual_is_comparison
#print axioms Erdos287.SP2Status.sp2_terminal_nodes_open
#print axioms Erdos287.SP2Status.sp2_external_interfaces_uninhabited
