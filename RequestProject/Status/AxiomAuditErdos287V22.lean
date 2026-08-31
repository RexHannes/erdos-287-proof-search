import Mathlib
import RequestProject.Status.Erdos287V22Status

/-!
# V22 axiom audit

`#print axioms` for every principal V22 declaration.  Only the standard Mathlib logical
principles `propext`, `Classical.choice`, `Quot.sound` may appear.  No external analytic
theorem enters through a user axiom, and no V22 file contains `sorry`, `admit`, `axiom`,
`opaque`, `unsafe`, `native_decide` or `@[implemented_by]`.
-/

-- Safe bad-character log ledger
#print axioms Erdos287.V22Ledger.cutoffOfB0_eq_sharedCutoff
#print axioms Erdos287.V22Ledger.cvar_doubled
#print axioms Erdos287.V22Ledger.cvar_doubled_at_one
#print axioms Erdos287.V22Ledger.cvar_doubled_at_two
#print axioms Erdos287.V22Ledger.cvar_doubled_at_three
#print axioms Erdos287.V22Ledger.cvar_at_one
#print axioms Erdos287.V22Ledger.cvar_at_two
#print axioms Erdos287.V22Ledger.cvar_at_three
#print axioms Erdos287.V22Ledger.cvar_decreasing_sample
#print axioms Erdos287.V22Ledger.cvar_le_channels

-- Ford-(7.23) candidate source adapter
#print axioms Erdos287.V22Ford.toPrimeBoxData_omega
#print axioms Erdos287.V22Ford.toPrimeBoxData_box
#print axioms Erdos287.V22Ford.ford723Adapter_transfers_prime_support
#print axioms Erdos287.V22Ford.ford723Adapter_transfers_pointwise
#print axioms Erdos287.V22Ford.ford723Adapter_not_automatic
#print axioms Erdos287.V22Ford.ford723Adapter_is_not_a_proof_of_the_source

-- Prime-box L¹ normalization
#print axioms Erdos287.V22PrimeBoxL1.primeBoxCardinality_not_automatic
#print axioms Erdos287.V22PrimeBoxL1.primeBoxL1_of_ford723Adapter
#print axioms Erdos287.V22PrimeBoxL1.primeBoxL1_compiler_cannot_construct_cardinality
#print axioms Erdos287.V22PrimeBoxL1.primeBoxL1_not_automatic_v22

-- Physical closure criterion
#print axioms Erdos287.V22Closure.netLogExponent_lt_neg_one_iff
#print axioms Erdos287.V22Closure.twoProjector_closes_of_cvar_gt_twoCext
#print axioms Erdos287.V22Closure.closure_capacity_B0_one
#print axioms Erdos287.V22Closure.closure_capacity_B0_two
#print axioms Erdos287.V22Closure.closure_fails_B0_three
#print axioms Erdos287.V22Closure.closure_at_zero_prefactor
#print axioms Erdos287.V22Closure.twoProjectorPhysical3221_closes_logVar
#print axioms Erdos287.V22Closure.twoProjectorPhysical3221_supplies_primeBoxL1
#print axioms Erdos287.V22Closure.physicalClosure_not_automatic
#print axioms Erdos287.V22Closure.physicalClosure_cannot_construct_comparison

-- V22 status ledger
#print axioms Erdos287.V22Status.badCharacter_d2_reledger_finite_pass
#print axioms Erdos287.V22Status.ford723_adapter_is_candidate_only
#print axioms Erdos287.V22Status.first_exact_residual_v22
#print axioms Erdos287.V22Status.comparison_still_not_first_residual_v22
#print axioms Erdos287.V22Status.terminal_nodes_open_v22
#print axioms Erdos287.V22Status.external_interfaces_uninhabited_v22
