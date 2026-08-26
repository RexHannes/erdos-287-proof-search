import RequestProject.TrustedBank.FixedAffine.Basic
import RequestProject.TrustedBank.FixedAffine.LocalRoots
import RequestProject.TrustedBank.FixedAffine.UnitTransport
import RequestProject.TrustedBank.FixedAffine.SingularFactors
import RequestProject.TrustedBank.FixedAffine.CofactorIntensity
import RequestProject.TrustedBank.FixedAffine.SymmetricPacket
import RequestProject.TrustedBank.Interfaces.ZeroSetTransport
import RequestProject.TrustedBank.Interfaces.FiniteSumTransport
import RequestProject.TrustedBank.Erdos287.BoundedCofactor
import RequestProject.TrustedBank.Erdos287.CarryTower
import RequestProject.TrustedBank.Erdos287.TopLayerConsequences
import RequestProject.Erdos287.Fiber
import RequestProject.Erdos287.Uniform
import RequestProject.TrustedBank.Gate1A.ScaleLedger
import RequestProject.TrustedBank.Gate1A.RowConservation
import RequestProject.TrustedBank.Gate1A.AvgJDRInterface
import RequestProject.TrustedBank.Gate1B.CenteredRho
import RequestProject.TrustedBank.Gate1B.MobiusCollapse
import RequestProject.TrustedBank.Gate1B.SeparableWeights
import RequestProject.TrustedBank.Gate1B.StartInjectivity
import RequestProject.TrustedBank.R9.Certificate
import RequestProject.TrustedBank.Erdos287.GoodPrime

/-!
# Audit — bank status

Axiom report for every theorem in `TrustedBank/`, plus the pre-existing Erdős #287
theorems the bank reuses.  Each `#print axioms` below must report only
`propext`, `Classical.choice`, `Quot.sound`.

This file contains no theorem of its own; it is the machine-checkable audit trail.
The human-readable table is `TRUSTED_BANK_AUDIT.md`.
-/

/-! ## Bank A — fixed-affine integer normal form -/
#print axioms TrustedBank.FixedAffine.affine_cross_identity
#print axioms TrustedBank.FixedAffine.affine_cross_identity_int
#print axioms TrustedBank.FixedAffine.root_transport
#print axioms TrustedBank.FixedAffine.first_root_iff
#print axioms TrustedBank.FixedAffine.second_root_iff
#print axioms TrustedBank.FixedAffine.normUnit_second_root
#print axioms TrustedBank.FixedAffine.normUnit_image_roots
#print axioms TrustedBank.FixedAffine.normUnit_ne_zero
#print axioms TrustedBank.FixedAffine.zmod_forbidden_pair

/-! ## Bank B — unit / finite-sum transport -/
#print axioms TrustedBank.UnitTransport.unitMul_bijective
#print axioms TrustedBank.UnitTransport.sum_unitMul
#print axioms TrustedBank.UnitTransport.unitMul_eq_zero_iff
#print axioms TrustedBank.UnitTransport.l2_energy_perm
#print axioms TrustedBank.UnitTransport.sum_perm
#print axioms TrustedBank.UnitTransport.kloostermanLike_unit_change

/-! ## Bank C — abstract SB fixed-unit portability -/
#print axioms TrustedBank.ZeroSetTransport.twist_eq_zero_iff
#print axioms TrustedBank.ZeroSetTransport.twist_simultaneous_zero_iff
#print axioms TrustedBank.ZeroSetTransport.twist_zeroSet_eq
#print axioms TrustedBank.ZeroSetTransport.twist_zeroSet_card_eq
#print axioms TrustedBank.ZeroSetTransport.twist_zeroSet_weighted_sum_eq
#print axioms TrustedBank.FiniteSumTransport.sum_equiv_transport
#print axioms TrustedBank.FiniteSumTransport.sum_le_transport
#print axioms TrustedBank.FiniteSumTransport.twisted_fibre_bound_transport

/-! ## Bank D — bounded-cofactor Bézout parametrisation -/
#print axioms TrustedBank.BoundedCofactor.Bez.key_identity
#print axioms TrustedBank.BoundedCofactor.Bez.dP_add_one
#print axioms TrustedBank.BoundedCofactor.Bez.isCoprime_d_e
#print axioms TrustedBank.BoundedCofactor.Bez.isCoprime_u_e
#print axioms TrustedBank.BoundedCofactor.Bez.isCoprime_v_d
#print axioms TrustedBank.BoundedCofactor.Bez.gcd_d_e
#print axioms TrustedBank.BoundedCofactor.Bez.gcd_u_e
#print axioms TrustedBank.BoundedCofactor.Bez.gcd_v_d

/-! ## Bank E — local admissibility -/
#print axioms TrustedBank.LocalRoots.linRoots_of_ne_zero
#print axioms TrustedBank.LocalRoots.linRoots_card_of_ne_zero
#print axioms TrustedBank.LocalRoots.linRoots_of_eq_zero
#print axioms TrustedBank.LocalRoots.no_two_nearby_roots
#print axioms TrustedBank.BoundedCofactor.Bez.exists_good_residue_of_three_le
#print axioms TrustedBank.BoundedCofactor.Bez.exists_good_residue_two
#print axioms TrustedBank.BoundedCofactor.Bez.two_obstructs_of_odd
#print axioms TrustedBank.BoundedCofactor.Bez.admissible_iff
#print axioms TrustedBank.BoundedCofactor.Bez.admissible_iff'

/-! ## Bank F — local singular factors -/
#print axioms TrustedBank.SingularFactors.rootSet_eq_union
#print axioms TrustedBank.SingularFactors.bez_zmod
#print axioms TrustedBank.SingularFactors.nu_eq_one
#print axioms TrustedBank.SingularFactors.nu_eq_two
#print axioms TrustedBank.SingularFactors.localFactor_ratio
#print axioms TrustedBank.SingularFactors.localFactor_of_dvd

/-! ## Bank G — cofactor intensity optimality -/
#print axioms TrustedBank.CofactorIntensity.two_mul_prod_le
#print axioms TrustedBank.CofactorIntensity.J_two
#print axioms TrustedBank.CofactorIntensity.J_le_half
#print axioms TrustedBank.CofactorIntensity.J_lt_half
#print axioms TrustedBank.CofactorIntensity.J_le_J_two
#print axioms TrustedBank.CofactorIntensity.J_eq_J_two_iff
#print axioms TrustedBank.CofactorIntensity.de_eq_two

/-! ## Bank H — symmetric ± projection -/
#print axioms TrustedBank.SymmetricPacket.odd_char_pair_cancel
#print axioms TrustedBank.SymmetricPacket.odd_char_symm_pair
#print axioms TrustedBank.SymmetricPacket.odd_char_symm_pair_weighted
#print axioms TrustedBank.SymmetricPacket.dirichlet_odd_symm_pair
#print axioms TrustedBank.SymmetricPacket.dirichlet_odd_symm_pair_weighted

/-! ## Erdős #287 — carry tower -/
#print axioms TrustedBank.CarryTower.factorization_finset_lcm
#print axioms TrustedBank.CarryTower.two_le_card_topLayer
#print axioms TrustedBank.CarryTower.exists_two_topLayer
#print axioms TrustedBank.CarryTower.pow_topExp_dvd_of_mem_topLayer
#print axioms TrustedBank.CarryTower.level_succ_subset
#print axioms TrustedBank.CarryTower.topLayer_subset_level
#print axioms TrustedBank.CarryTower.level_succ_topExp_eq_empty
#print axioms TrustedBank.CarryTower.lcm_sq_dvd_prod
#print axioms TrustedBank.CarryTower.lcm_dvd_pairwise_diff_prod
#print axioms TrustedBank.CarryTower.lcm_sq_not_dvd_prod_general
#print axioms TrustedBank.CarryTower.lcm_not_dvd_diff_general

/-! ## Erdős #287 — generalized fixed-cofactor blocker -/
#print axioms TrustedBank.Erdos287Blockers.Gap2CE.blocker_of_excluded_neighbour_sub
#print axioms TrustedBank.Erdos287Blockers.Gap2CE.blocker_of_excluded_neighbour_add
#print axioms TrustedBank.Erdos287Blockers.Gap2CE.fixedCofactor_blocker_sub
#print axioms TrustedBank.Erdos287Blockers.Gap2CE.fixedCofactor_blocker_add
#print axioms TrustedBank.Erdos287Blockers.Gap2CE.fixedCofactor_blocker_sub_sharpWindow
#print axioms TrustedBank.Erdos287Blockers.Gap2CE.fixedCofactor_blocker_add_sharpWindow

/-! ## Reused pre-existing Erdős #287 bank -/
#print axioms Erdos287.topLayer_congruence
#print axioms Erdos287.topLayer_card_ne_one
#print axioms Erdos287.topLayer_two_obstruction
#print axioms Erdos287.topLayer_three_obstruction
#print axioms Erdos287.topLayer_symm_congruence
#print axioms Erdos287.primePower_window_exclusion
#print axioms Erdos287.C_values
#print axioms Erdos287.C_seven_witness
#print axioms Erdos287.Gap2CE.blockerPair_contradiction
#print axioms Erdos287.Gap2CE.primeFree
#print axioms Erdos287.Gap2CE.goodPrime_blocker_sub
#print axioms Erdos287.Gap2CE.goodPrime_blocker_add

/-! ## Uniform numerator bounds (previously `sorry`-ed, now proved) -/
#print axioms Erdos287.C_le_lcm_mul_harmonic
#print axioms Erdos287.harmonic_le_nat
#print axioms Erdos287.C_le_U
#print axioms Erdos287.primePower_window_exclusion_U
#print axioms Erdos287.Gap2CE.forcedHole_not_mem
#print axioms Erdos287.Gap2CE.forcedHole_pair_contradiction

/-! ## Δv6 — Gate 1A finite bank -/
#print axioms TrustedBank.Gate1A.naturalEnergy_sub_targetEnergy
#print axioms TrustedBank.Gate1A.missingRatio_vertices
#print axioms TrustedBank.Gate1A.missingRatio_pos
#print axioms TrustedBank.Gate1A.expH_eq
#print axioms TrustedBank.Gate1A.expK_eq
#print axioms TrustedBank.Gate1A.massSq_rowVec
#print axioms TrustedBank.Gate1A.total_massSq_rowVec
#print axioms TrustedBank.Gate1A.total_massSq_pos
#print axioms TrustedBank.Gate1A.massSq_comp_equiv
#print axioms TrustedBank.Gate1A.massSq_diagonal_unit
#print axioms TrustedBank.Gate1A.massSq_sum_type
#print axioms TrustedBank.Gate1A.massSq_unitary
#print axioms TrustedBank.Gate1A.total_massSq_reorganisation_invariant
#print axioms TrustedBank.Gate1A.avgJDR_transfer_exact
#print axioms TrustedBank.Gate1A.avgJDR_transfer
#print axioms TrustedBank.Gate1A.avgJDR_normalized

/-! ## Δv6 — Gate 1B centered product algebra -/
#print axioms TrustedBank.Gate1B.rho_sum_period
#print axioms TrustedBank.Gate1B.rho_mul_of_coprime
#print axioms TrustedBank.Gate1B.rho_not_multiplicative_of_not_coprime
#print axioms TrustedBank.Gate1B.moebius_of_prime_times_squarefree
#print axioms TrustedBank.Gate1B.coprime_div_prime
#print axioms TrustedBank.Gate1B.moebius_div_prime
#print axioms TrustedBank.Gate1B.mmd_clean_collapse
#print axioms TrustedBank.Gate1B.moebius_prime_sq_eq_zero
#print axioms TrustedBank.Gate1B.moebius_div_prime_fails_at_prime_square
#print axioms TrustedBank.Gate1B.sourceMMD_clean_cell
#print axioms TrustedBank.Gate1B.SeparableWeightDecomposition.sum_expand
#print axioms TrustedBank.Gate1B.SeparableWeightDecomposition.mmd_cost_bound
#print axioms TrustedBank.Gate1B.sameStart_injective
#print axioms TrustedBank.Gate1B.sameStart_injective_mod
#print axioms TrustedBank.Gate1B.mixedStart_not_diagonal

/-! ## Δv6 — R9 finite certificate -/
#print axioms TrustedBank.R9.altSum_eq
#print axioms TrustedBank.R9.Hg_value_of_formula
#print axioms TrustedBank.R9.Hg_value_one

/-! ## Δv6 — Erdős #287 good-prime bank -/
#print axioms TrustedBank.Erdos287Good.GoodPrime.excludedPP
#print axioms TrustedBank.Erdos287Good.goodPrimeExclusion
#print axioms TrustedBank.Erdos287Good.goodPrime_fibre_empty
#print axioms TrustedBank.Erdos287Good.Gap2CE.goodPrime_adjacent_holes
#print axioms TrustedBank.Erdos287Good.Gap2CE.goodPrime_adjacent_blocker
#print axioms TrustedBank.Erdos287Good.Gap2CE.goodPrime_adjacent_blocker_upper_half
#print axioms TrustedBank.Erdos287Good.Gap2CE.goodPrime_of_window_bound
#print axioms TrustedBank.Erdos287Good.Gap2CE.logCofactor_finite_blocker
