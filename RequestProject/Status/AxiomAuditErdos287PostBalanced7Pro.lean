import Mathlib
import RequestProject.Status.CurrentStatusErdos287PostBalanced7Pro

/-!
# Axiom audit — Erdős #287, post-Balanced7 "Pro" pass

`#print axioms` for every principal declaration added by this pass.  Only `propext`,
`Classical.choice` and `Quot.sound` may appear.  No analytic or source interface is
inhabited, and no file of this layer contains `sorry`, `admit`, `axiom`, `opaque`, `unsafe`,
`native_decide` or `@[implemented_by]`.
-/

-- §3  seven-box prime weights
#print axioms Erdos287.PostBalanced7Pro.norm_omegaBox_eq_V
#print axioms Erdos287.PostBalanced7Pro.norm_omegaBox_le_one
#print axioms Erdos287.PostBalanced7Pro.omegaBox_support_is_primes

-- §4  prime-tuple multiplicity
#print axioms Erdos287.PostBalanced7Pro.prime_tuple_perm
#print axioms Erdos287.PostBalanced7Pro.card_prodFiber_le_factorial
#print axioms Erdos287.PostBalanced7Pro.representationMultiplicity_le_factorial
#print axioms Erdos287.PostBalanced7Pro.representationMultiplicity3_le_six
#print axioms Erdos287.PostBalanced7Pro.representationMultiplicity4_le_twentyfour
#print axioms Erdos287.PostBalanced7Pro.a3_sq_sum_le_six
#print axioms Erdos287.PostBalanced7Pro.b4_sq_sum_le_twentyfour
#print axioms Erdos287.PostBalanced7Pro.convWeightC_sq_sum_le
#print axioms Erdos287.PostBalanced7Pro.seven_box_energy_bound

-- §5  conductor-split multiplicative large sieve
#print axioms Erdos287.PostBalanced7Pro.condSum_nonneg
#print axioms Erdos287.PostBalanced7Pro.condSum_add_highCondSum
#print axioms Erdos287.PostBalanced7Pro.condSplit_disjoint
#print axioms Erdos287.PostBalanced7Pro.condSum_le_fullCondSum
#print axioms Erdos287.PostBalanced7Pro.condSum_mono
#print axioms Erdos287.PostBalanced7Pro.sum_moebius_divisors
#print axioms Erdos287.PostBalanced7Pro.coprime_indicator_eq
#print axioms Erdos287.PostBalanced7Pro.conductorLargeSieve_full_bound
#print axioms Erdos287.PostBalanced7Pro.conductorLargeSieve_not_automatic

-- §6  tiny-modulus Siegel–Walfisz child
#print axioms Erdos287.PostBalanced7Pro.lowConductorCutoff_mono
#print axioms Erdos287.PostBalanced7Pro.lowConductorCutoff_ne_uCut
#print axioms Erdos287.PostBalanced7Pro.lowConductorCutoff_ne_uCut_fun
#print axioms Erdos287.PostBalanced7Pro.lowConductor_aggregate_bound
#print axioms Erdos287.PostBalanced7Pro.lowConductorSiegelWalfisz_not_automatic
#print axioms Erdos287.PostBalanced7Pro.lowConductor_effectivity_firewall

-- §7  SmallQ 3+4 conditional compiler
#print axioms Erdos287.PostBalanced7Pro.smallQ34LS_compiler
#print axioms Erdos287.PostBalanced7Pro.smallQ34LS_compiler_pointwise
#print axioms Erdos287.PostBalanced7Pro.smallQ34LSInputs_not_automatic
#print axioms Erdos287.PostBalanced7Pro.smallQ34LS_residual_is_normalisation

-- §12–§15  small-prime prefix
#print axioms Erdos287.PostBalanced7Pro.zZero_pow
#print axioms Erdos287.PostBalanced7Pro.smoothPart_mul_roughPart
#print axioms Erdos287.PostBalanced7Pro.smoothPart_smooth
#print axioms Erdos287.PostBalanced7Pro.roughPart_rough
#print axioms Erdos287.PostBalanced7Pro.coprime_smooth_rough
#print axioms Erdos287.PostBalanced7Pro.smoothRough_unique
#print axioms Erdos287.PostBalanced7Pro.prefix_dichotomy
#print axioms Erdos287.PostBalanced7Pro.smoothPrefix_three_firewall
#print axioms Erdos287.PostBalanced7Pro.truncMoebius_two_two
#print axioms Erdos287.PostBalanced7Pro.truncMoebius_two_three
#print axioms Erdos287.PostBalanced7Pro.truncMoebius_not_prefix_factorisable
#print axioms Erdos287.PostBalanced7Pro.rGeThreePrefix_split
#print axioms Erdos287.PostBalanced7Pro.threeSmallPrimePrefix_not_automatic

-- §10  post-repair owner map and compiler
#print axioms Erdos287.PostBalanced7Pro.postRepairOwnerMap_is_the_mandated_one
#print axioms Erdos287.PostBalanced7Pro.postRepairOwner_exists_unique
#print axioms Erdos287.PostBalanced7Pro.postRepairOwner_is_a_refinement
#print axioms Erdos287.PostBalanced7Pro.postRepair_no_double_spending
#print axioms Erdos287.PostBalanced7Pro.postRepair_accounts_disjoint
#print axioms Erdos287.PostBalanced7Pro.postRepair_smallQ_account
#print axioms Erdos287.PostBalanced7Pro.postRepair_threePrefix_account
#print axioms Erdos287.PostBalanced7Pro.balancedSeven_postRepair_compiler
#print axioms Erdos287.PostBalanced7Pro.postRepairInputs_not_inhabited_here
#print axioms Erdos287.PostBalanced7Pro.postRepair_compiler_does_not_prove_balancedSeven

-- §16  K0 uniform fragmentation compiler
#print axioms Erdos287.PostBalanced7Pro.k0_uniform_fragmentation_compiler
#print axioms Erdos287.PostBalanced7Pro.k0FragmentationInputs_not_inhabited_here
#print axioms Erdos287.PostBalanced7Pro.k0_residual_is_three_prefix
#print axioms Erdos287.PostBalanced7Pro.k0_not_activated

-- §11  status ledger
#print axioms Erdos287.PostBalanced7ProStatus.no_closed_rows
#print axioms Erdos287.PostBalanced7ProStatus.erdos287_open
#print axioms Erdos287.PostBalanced7ProStatus.balanced7_open
#print axioms Erdos287.PostBalanced7ProStatus.k0_is_reduced_not_closed
#print axioms Erdos287.PostBalanced7ProStatus.first_downstream_residual_is_three_smallprime_prefix
#print axioms Erdos287.PostBalanced7ProStatus.first_residual_is_smallq_34LS_normalisation
#print axioms Erdos287.PostBalanced7ProStatus.effectivity_firewall
#print axioms Erdos287.PostBalanced7ProStatus.ledger_is_honest
#print axioms Erdos287.PostBalanced7ProStatus.downstream_not_activated
