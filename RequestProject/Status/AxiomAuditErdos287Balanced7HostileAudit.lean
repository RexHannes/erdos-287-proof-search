import Mathlib
import RequestProject.Status.CurrentStatusErdos287Balanced7HostileAudit

/-!
# Axiom audit — Erdős #287, Balanced7 hostile-audit safe bank

`#print axioms` for every principal declaration added by this pass.  Only `propext`,
`Classical.choice` and `Quot.sound` may appear.  No analytic or source interface of this
layer is inhabited, and no file of this layer contains `sorry`, `admit`, `axiom`, `opaque`,
`unsafe`, `native_decide` or `@[implemented_by]`.
-/

-- §2  SP-2 → seven-box source adapter
#print axioms Erdos287.HostileAudit.squarefree_prod_of_primes
#print axioms Erdos287.HostileAudit.cardFactors_eq_card_primeFactors
#print axioms Erdos287.HostileAudit.truncMobius_of_primeProduct
#print axioms Erdos287.HostileAudit.subsetAlternatingSum_eq_binomial
#print axioms Erdos287.HostileAudit.truncMobius_sevenBox_eq_neg20
#print axioms Erdos287.HostileAudit.truncMobius_sevenBox_matches_counterguard
#print axioms Erdos287.HostileAudit.sevenBox_alternating_expansion
#print axioms Erdos287.HostileAudit.boxWeight_eq_omegaBox
#print axioms Erdos287.HostileAudit.norm_boxWeight_le_one
#print axioms Erdos287.HostileAudit.boxWeight_support_is_primes
#print axioms Erdos287.HostileAudit.seal_pointwise_law
#print axioms Erdos287.HostileAudit.seal_prime_support
#print axioms Erdos287.HostileAudit.seal_certificate_value_neg20
#print axioms Erdos287.HostileAudit.seal_rigidity
#print axioms Erdos287.HostileAudit.sp2SourceSeal_not_automatic

-- §3  general-modulus induced-character algebra
#print axioms Erdos287.HostileAudit.coprime_mul_split
#print axioms Erdos287.HostileAudit.induced_character_pointwise
#print axioms Erdos287.HostileAudit.inducedSpec_holds_for_nonSquarefree_modulus
#print axioms Erdos287.HostileAudit.induced_character_nonSquarefree_instance
#print axioms Erdos287.HostileAudit.gcd_divisors_eq_filter
#print axioms Erdos287.HostileAudit.coprimeIndicator_moebius_expansion
#print axioms Erdos287.HostileAudit.moebius_expansion_nonSquarefree_j_four
#print axioms Erdos287.HostileAudit.induced_character_moebius_form

-- §4  totient / complementary-factor algebra
#print axioms Erdos287.HostileAudit.totient_mul_ge
#print axioms Erdos287.HostileAudit.totient_gcd_exact
#print axioms Erdos287.HostileAudit.complementary_factor_bound
#print axioms Erdos287.HostileAudit.complementary_factor_bound_window
#print axioms Erdos287.HostileAudit.complementary_factor_saving_is_real
#print axioms Erdos287.HostileAudit.divisorVariable_ne_complementaryFactor
#print axioms Erdos287.HostileAudit.divisor_expansion_uses_proper_divisors

-- §5  general-modulus conductor-split compiler
#print axioms Erdos287.HostileAudit.window_gives_complementary_bound
#print axioms Erdos287.HostileAudit.general_modulus_cell_bound
#print axioms Erdos287.HostileAudit.general_modulus_conductorSplit_compiler
#print axioms Erdos287.HostileAudit.primitiveLargeSieve_not_automatic
#print axioms Erdos287.HostileAudit.divisorSumPolylog_not_automatic
#print axioms Erdos287.HostileAudit.general_modulus_compiler_is_conditional

-- §7  SmallR owner / capacity
#print axioms Erdos287.HostileAudit.smallR_defect_eq_source_sub_principal
#print axioms Erdos287.HostileAudit.smallR_source_eq_principal_add_defect
#print axioms Erdos287.HostileAudit.smallR_owner_pair_is_exact
#print axioms Erdos287.HostileAudit.smallR_owner_assignment
#print axioms Erdos287.HostileAudit.smallR_owners_are_distinct
#print axioms Erdos287.HostileAudit.smallR_defect_account
#print axioms Erdos287.HostileAudit.smallR_modulus_capacity
#print axioms Erdos287.HostileAudit.smallR_exponent_ledger
#print axioms Erdos287.HostileAudit.smallR_principal_of_capacity_input
#print axioms Erdos287.HostileAudit.smallRPrincipalCapacity_not_automatic

-- §8  short-`t` residue geometry
#print axioms Erdos287.HostileAudit.shortT_unique_forbidden_class
#print axioms Erdos287.HostileAudit.shortT_forbidden_class_formula
#print axioms Erdos287.HostileAudit.shortT_constant_class_of_dvd
#print axioms Erdos287.HostileAudit.shortT_dvd_case_is_all_or_nothing
#print axioms Erdos287.HostileAudit.shortT_scale_ledger
#print axioms Erdos287.HostileAudit.shortT_scale_separation_real
#print axioms Erdos287.HostileAudit.smallPrime_not_dividing_YscaleProduct
#print axioms Erdos287.HostileAudit.shortT_sieve_primes_disjoint_from_boxes
#print axioms Erdos287.HostileAudit.shortTSieve_still_uninhabited

-- §9  Shiu hypothesis compiler
#print axioms Erdos287.HostileAudit.shiu_exponent_margin
#print axioms Erdos287.HostileAudit.shiu_modulus_within_admissible_range
#print axioms Erdos287.HostileAudit.shiu_margin_is_strict
#print axioms Erdos287.HostileAudit.shiu_shift_coprime
#print axioms Erdos287.HostileAudit.shiu_shift_coprime_nat
#print axioms Erdos287.HostileAudit.shiu_target_of_input
#print axioms Erdos287.HostileAudit.shiu_input_still_uninhabited

-- §10  raw-raw / cross variance compiler
#print axioms Erdos287.HostileAudit.rawRaw_variance_bound
#print axioms Erdos287.HostileAudit.rawRaw_saving_is_five_not_ten
#print axioms Erdos287.HostileAudit.cross_variance_bound
#print axioms Erdos287.HostileAudit.variance_exponent_ledger

-- §11  hard amplitude exponent compiler
#print axioms Erdos287.HostileAudit.hard_amplitude_exponent_ledger
#print axioms Erdos287.HostileAudit.hard_amplitude_product
#print axioms Erdos287.HostileAudit.cext_is_one
#print axioms Erdos287.HostileAudit.hard_cell_log_budget
#print axioms Erdos287.HostileAudit.hard_dyadic_summation
#print axioms Erdos287.HostileAudit.hard_budget_is_not_a_closure
#print axioms Erdos287.HostileAudit.hardAmplitudeAsymptotic_not_automatic

-- §12  full-`q` exact reassembly
#print axioms Erdos287.HostileAudit.fullQ_exact_cover
#print axioms Erdos287.HostileAudit.fullQ_pairwise_disjoint
#print axioms Erdos287.HostileAudit.boundary_q_eq_U_is_smallQ
#print axioms Erdos287.HostileAudit.boundary_r_eq_U_is_smallR
#print axioms Erdos287.HostileAudit.region_source_split
#print axioms Erdos287.HostileAudit.region_defect_is_the_subtraction
#print axioms Erdos287.HostileAudit.region_principals_sum_eq_full
#print axioms Erdos287.HostileAudit.no_region_owns_the_full_principal
#print axioms Erdos287.HostileAudit.fullQ_owner_exists_unique
#print axioms Erdos287.HostileAudit.fullQ_no_double_spending
#print axioms Erdos287.HostileAudit.fullQ_euler_account_is_the_three_principals
#print axioms Erdos287.HostileAudit.even_q_is_impossible
#print axioms Erdos287.HostileAudit.q_coprime_twoP
#print axioms Erdos287.HostileAudit.routing_is_exhaustive

-- §13  Balanced7 conditional closure compiler
#print axioms Erdos287.HostileAudit.balancedSeven_hostileAudit_compiler
#print axioms Erdos287.HostileAudit.hostileAuditInputs_not_inhabited_here
#print axioms Erdos287.HostileAudit.hostile_audit_is_not_a_lean_proof
#print axioms Erdos287.HostileAudit.hostileAudit_analytic_children_are_uninhabited

-- §15  effectivity socket
#print axioms Erdos287.HostileAudit.effective_smallQ_lowConductor_of_input
#print axioms Erdos287.HostileAudit.effective_input_has_no_exceptional_case
#print axioms Erdos287.HostileAudit.effective_socket_supplies_a_threshold
#print axioms Erdos287.HostileAudit.effective_socket_is_not_siegelWalfisz
#print axioms Erdos287.HostileAudit.effectiveLowConductor_not_automatic

-- §14  status ledger
#print axioms Erdos287.Balanced7HostileAuditStatus.no_closed_rows
#print axioms Erdos287.Balanced7HostileAuditStatus.erdos287_open
#print axioms Erdos287.Balanced7HostileAuditStatus.externallyAudited_is_not_proved
#print axioms Erdos287.Balanced7HostileAuditStatus.balanced7_is_audited_not_proved
#print axioms Erdos287.Balanced7HostileAuditStatus.death_certificates_retracted
#print axioms Erdos287.Balanced7HostileAuditStatus.first_mainline_residual_is_three_smallprime_prefix
#print axioms Erdos287.Balanced7HostileAuditStatus.source_seal_is_open
#print axioms Erdos287.Balanced7HostileAuditStatus.effectivity_socket_is_open
#print axioms Erdos287.Balanced7HostileAuditStatus.downstream_frontier_preserved
#print axioms Erdos287.Balanced7HostileAuditStatus.ledger_is_honest
#print axioms Erdos287.Balanced7HostileAuditStatus.rawRaw_row_uses_the_corrected_exponent
