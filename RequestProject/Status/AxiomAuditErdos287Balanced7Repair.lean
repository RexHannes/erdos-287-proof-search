import Mathlib
import RequestProject.Status.CurrentStatusErdos287Balanced7Repair

/-!
# Axiom audit — Erdős #287 Balanced7 post-audit repair

`#print axioms` for every principal declaration of the `CurrentProgramme` repair layer.
Only `propext`, `Classical.choice` and `Quot.sound` may appear.  No analytic or source
interface is inhabited, and no file of this layer contains `sorry`, `admit`, `axiom`,
`opaque`, `unsafe`, `native_decide` or `@[implemented_by]`.
-/

-- §2  log-`r` repair bank
#print axioms Erdos287.CurrentProgramme.vonMangoldt_eq_sum_moebius_mul_logR
#print axioms Erdos287.CurrentProgramme.affine_vonMangoldt_eq_sum_moebius_mul_logR
#print axioms Erdos287.CurrentProgramme.cExtCurrent_eq_one
#print axioms Erdos287.CurrentProgramme.cExtRetracted_ne_cExtCurrent
#print axioms Erdos287.CurrentProgramme.cExt_retraction_is_a_theorem
#print axioms Erdos287.CurrentProgramme.cVarCurrent_eq_five
#print axioms Erdos287.CurrentProgramme.logR_signed_margin
#print axioms Erdos287.CurrentProgramme.logR_net_exponent
#print axioms Erdos287.CurrentProgramme.logR_ledger_does_not_give_analytic

-- §3  Euler-uniformity firewall
#print axioms Erdos287.CurrentProgramme.jFullQ_split
#print axioms Erdos287.CurrentProgramme.eulerQRange_is_unrestricted
#print axioms Erdos287.CurrentProgramme.fullQ_identity_not_single_cell
#print axioms Erdos287.CurrentProgramme.jFullQ_not_smallQ_cell
#print axioms Erdos287.CurrentProgramme.fullQEulerIdentity_consumer
#print axioms Erdos287.CurrentProgramme.fullQEulerIdentity_not_automatic
#print axioms Erdos287.CurrentProgramme.fullQEuler_status_is_external

-- §4  exact q/r partition
#print axioms Erdos287.CurrentProgramme.qr_exact_cover
#print axioms Erdos287.CurrentProgramme.qr_exact_pairwise_disjoint
#print axioms Erdos287.CurrentProgramme.qr_exact_unique_sector
#print axioms Erdos287.CurrentProgramme.sectorOf_eq_smallQ_iff
#print axioms Erdos287.CurrentProgramme.sectorOf_eq_smallR_iff
#print axioms Erdos287.CurrentProgramme.sectorOf_eq_hard_iff
#print axioms Erdos287.CurrentProgramme.qr_unique_sharp_ownership
#print axioms Erdos287.CurrentProgramme.qr_cells_cover_factorisations
#print axioms Erdos287.CurrentProgramme.qr_cells_pairwise_disjoint
#print axioms Erdos287.CurrentProgramme.qr_exact_reassembly
#print axioms Erdos287.CurrentProgramme.qr_cardinality_reassembly
#print axioms Erdos287.CurrentProgramme.hard_cell_forces_U_sq_lt_N
#print axioms Erdos287.CurrentProgramme.hard_cell_empty_of_N_le_U_sq
#print axioms Erdos287.CurrentProgramme.smallQ_smallR_are_not_interchangeable

-- §7  finite 3+4 product algebra
#print axioms Erdos287.CurrentProgramme.convWeight_sum_eq
#print axioms Erdos287.CurrentProgramme.sum_prod_sq_eq_prod_energy
#print axioms Erdos287.CurrentProgramme.prodFiber_fibrewise_sq
#print axioms Erdos287.CurrentProgramme.convWeight_sq_le_fiber
#print axioms Erdos287.CurrentProgramme.convWeight_sq_sum_le
#print axioms Erdos287.CurrentProgramme.a3_sq_sum_le
#print axioms Erdos287.CurrentProgramme.b4_sq_sum_le
#print axioms Erdos287.CurrentProgramme.labelled_multiplicity_exceeds_one
#print axioms Erdos287.CurrentProgramme.repeated_primes_are_included
#print axioms Erdos287.CurrentProgramme.representationMultiplicity_ge_two
#print axioms Erdos287.CurrentProgramme.threePlusFourDensity_not_automatic

-- §5–§6  SmallQ route and 3+4 source socket
#print axioms Erdos287.CurrentProgramme.dvd_shift_of_dvd_affine_and_base
#print axioms Erdos287.CurrentProgramme.smallQ_source_mismatch
#print axioms Erdos287.CurrentProgramme.smallQ_route_superseded
#print axioms Erdos287.CurrentProgramme.smallQ_supersession_is_not_refutation
#print axioms Erdos287.CurrentProgramme.smallQ34LS_consumer
#print axioms Erdos287.CurrentProgramme.smallQ34LS_not_automatic
#print axioms Erdos287.CurrentProgramme.smallQ34LS_is_first_exact_residual

-- §8  imprimitive conductor bookkeeping
#print axioms Erdos287.CurrentProgramme.conductor_dvd_level'
#print axioms Erdos287.CurrentProgramme.moebius_ne_zero_squarefree_level
#print axioms Erdos287.CurrentProgramme.conductor_mem_divisors
#print axioms Erdos287.CurrentProgramme.conductor_lift_count_le_divisor_count
#print axioms Erdos287.CurrentProgramme.q_over_phi_ge_one
#print axioms Erdos287.CurrentProgramme.character_vanishes_on_nonunits
#print axioms Erdos287.CurrentProgramme.conductorRecord_level_pos
#print axioms Erdos287.CurrentProgramme.conductorRecord_conductor_le_level
#print axioms Erdos287.CurrentProgramme.imprimitiveConductor_not_automatic

-- §9  SmallR owner subtraction
#print axioms Erdos287.CurrentProgramme.smallR_owner_subtraction
#print axioms Erdos287.CurrentProgramme.smallR_defect_unique
#print axioms Erdos287.CurrentProgramme.smallR_defect_bound
#print axioms Erdos287.CurrentProgramme.smallR_reassembly_from_defect
#print axioms Erdos287.CurrentProgramme.smallR_defect_of_analytic_input
#print axioms Erdos287.CurrentProgramme.smallRDefectAnalytic_not_automatic

-- §10  hard-θ δ = 1/21
#print axioms Erdos287.CurrentProgramme.hardDelta_lower_endpoint
#print axioms Erdos287.CurrentProgramme.hardDelta_upper_endpoint
#print axioms Erdos287.CurrentProgramme.hardLogScale_eq
#print axioms Erdos287.CurrentProgramme.hardDelta_pos
#print axioms Erdos287.CurrentProgramme.hard_physical_range_delta
#print axioms Erdos287.CurrentProgramme.log_hardZ_eq
#print axioms Erdos287.CurrentProgramme.log_hardZ_lower_bound
#print axioms Erdos287.CurrentProgramme.log_hardZ_pos
#print axioms Erdos287.CurrentProgramme.inv_log_hardZ_bound
#print axioms Erdos287.CurrentProgramme.physical_range_budget_of_sieve_saving
#print axioms Erdos287.CurrentProgramme.no_uniform_delta_on_open_interval
#print axioms Erdos287.CurrentProgramme.hardDelta_range_is_not_the_open_interval

-- §11  short-t and Shiu sockets
#print axioms Erdos287.CurrentProgramme.shortT_physical_budget
#print axioms Erdos287.CurrentProgramme.shortTSieve_not_automatic
#print axioms Erdos287.CurrentProgramme.shortT_saving_is_not_logX
#print axioms Erdos287.CurrentProgramme.affineSeq_apply
#print axioms Erdos287.CurrentProgramme.shiu_consumer
#print axioms Erdos287.CurrentProgramme.shiu_not_automatic

-- §12  owner map
#print axioms Erdos287.CurrentProgramme.ownerMap_is_the_mandated_one
#print axioms Erdos287.CurrentProgramme.owner_exists_unique
#print axioms Erdos287.CurrentProgramme.owner_map_not_injective
#print axioms Erdos287.CurrentProgramme.no_double_spending
#print axioms Erdos287.CurrentProgramme.owner_cells_pairwise_disjoint
#print axioms Erdos287.CurrentProgramme.owner_cells_cover
#print axioms Erdos287.CurrentProgramme.euler_principal_account
#print axioms Erdos287.CurrentProgramme.zero_routed_account

-- §13  post-audit full-q compiler
#print axioms Erdos287.CurrentProgramme.balancedSeven_postAudit_compiler
#print axioms Erdos287.CurrentProgramme.postAuditInputs_not_inhabited_here
#print axioms Erdos287.CurrentProgramme.postAudit_compiler_does_not_prove_balancedSeven

-- §16  status ledger
#print axioms Erdos287.Balanced7RepairStatus.no_closed_rows
#print axioms Erdos287.Balanced7RepairStatus.erdos287_open
#print axioms Erdos287.Balanced7RepairStatus.balanced7_open
#print axioms Erdos287.Balanced7RepairStatus.first_residual_is_smallq_34LS_normalisation
#print axioms Erdos287.Balanced7RepairStatus.ledger_is_honest
#print axioms Erdos287.Balanced7RepairStatus.effectivity_firewall
#print axioms Erdos287.Balanced7RepairStatus.downstream_not_activated
#print axioms Erdos287.Balanced7RepairStatus.euler_uniformity_is_externally_audited_only
