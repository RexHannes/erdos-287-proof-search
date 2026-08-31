import Mathlib
import RequestProject.Status.Erdos287V20Status

/-!
# Erdős #287 — V20 axiom audit

`#print axioms` for every principal V20 declaration.  Only `propext`, `Classical.choice`
and `Quot.sound` may appear; no `axiom`, `opaque`, `unsafe`, `native_decide` or
`@[implemented_by]` is used anywhere in the V20 bank, and no analytic or source interface
is inhabited (in particular none is inhabited through `Classical.choice` or an artificial
constructor — the interfaces below have *no* inhabitants at all).
-/

namespace Erdos287
namespace V20Audit

section AxiomAudit

-- Phase A: the high-conductor character set and the inverse-sampled character algebra
#print axioms Erdos287.V20Gram.mem_highSet_iff_lt_conductor
#print axioms Erdos287.V20Gram.sum_highSet_eq_sum_ite
#print axioms Erdos287.V20Gram.affineSample_mul_eq_one
#print axioms Erdos287.V20Gram.affineSample_isUnit
#print axioms Erdos287.V20Gram.affineSample_inv
#print axioms Erdos287.V20Gram.conj_char_apply
#print axioms Erdos287.V20Gram.conj_char_eq_inv_char
#print axioms Erdos287.V20Gram.affineSample_character_factor
#print axioms Erdos287.V20Gram.inverseSample_character_identity
#print axioms Erdos287.V20Gram.cHigh_inverseSampled_expansion
#print axioms Erdos287.V20Gram.charSrc_eq_cHigh_inverseSampled

-- Phase C: the exact m-sampled character Gram
#print axioms Erdos287.V20Gram.autocorr_reindex
#print axioms Erdos287.V20Gram.charSource_variance_eq_gram
#print axioms Erdos287.V20Gram.inverseSampledVariance_eq_characterGram
#print axioms Erdos287.V20Gram.fixedModulus_samePrimitive_induced_unique
#print axioms Erdos287.V20Gram.fixedModulus_ne_of_lift_ne

-- Phase D/F: diagonal split, Parseval, Young, separate-L² death certificate
#print axioms Erdos287.V20Gram.characterGram_diag_split
#print axioms Erdos287.V20Gram.autocorr_principal_eq_energy
#print axioms Erdos287.V20Gram.autocorr_principal_highCoeff
#print axioms Erdos287.V20Gram.gram_parseval
#print axioms Erdos287.V20Gram.energy_shift_invariant
#print axioms Erdos287.V20Gram.autocorr_sup_le
#print axioms Erdos287.V20Gram.autocorr_l2_sq_le
#print axioms Erdos287.V20Gram.separateL2_compiler
#print axioms Erdos287.V20Gram.separateGramL2_capacity_deficit

-- Phase B: the five-box character factorisation
#print axioms Erdos287.V20FiveBox.sum_mul_sum5
#print axioms Erdos287.V20FiveBox.pairBlockSum_eq_mul
#print axioms Erdos287.V20FiveBox.fiveBox_characterTransform_eq_prod_five
#print axioms Erdos287.V20FiveBox.fiveBox_characterTransform_factor
#print axioms Erdos287.V20FiveBox.highCoeff_fiveBox
#print axioms Erdos287.V20FiveBox.highCoeff_of_not_high

-- Phases D/E/G/H: children, capacity firewalls, router
#print axioms Erdos287.V20Router.largeSieve_not_automatic
#print axioms Erdos287.V20Router.highCondDiagonal_of_largeSieve
#print axioms Erdos287.V20Router.diagonal_power_room_rational
#print axioms Erdos287.V20Router.diagonal_power_room_rpow
#print axioms Erdos287.V20Router.lowConductor_card_le
#print axioms Erdos287.V20Router.lowQuotient_child_le
#print axioms Erdos287.V20Router.lowQuotient_child_of_diagonal_budget
#print axioms Erdos287.V20Router.pointwiseBurgess_not_automatic
#print axioms Erdos287.V20Router.pointwiseBurgess_capacity_deficit
#print axioms Erdos287.V20Router.conductorCell_routed
#print axioms Erdos287.V20Router.router_case_A
#print axioms Erdos287.V20Router.router_case_B
#print axioms Erdos287.V20Router.router_case_C
#print axioms Erdos287.V20Router.router_threshold_identity
#print axioms Erdos287.V20Router.router_case_A_slack

-- Phase I: the HHH surviving region, the exact Gram object and the open socket
#print axioms Erdos287.V20HHH.HHHGramData.mem_survivingChiSet_iff
#print axioms Erdos287.V20HHH.HHHGramData.survivingCell_of_mem
#print axioms Erdos287.V20HHH.probeHHHData_gram
#print axioms Erdos287.V20HHH.hhhGram_input_not_automatic
#print axioms Erdos287.V20HHH.logVar_of_four_channels
#print axioms Erdos287.V20HHH.logVar_does_not_construct_hhh

-- Phase J: the sixth-moment sufficient bridge
#print axioms Erdos287.V20Sixth.sixthMoment_nonneg
#print axioms Erdos287.V20Sixth.injOn_affineSample
#print axioms Erdos287.V20Sixth.sampled_sixth_le
#print axioms Erdos287.V20Sixth.sixthMoment_holder_at
#print axioms Erdos287.V20Sixth.sixthMoment_holder_over_q
#print axioms Erdos287.V20Sixth.sixthMoment_input_not_automatic
#print axioms Erdos287.V20Sixth.sixthMoment_variance_exponent
#print axioms Erdos287.V20Sixth.sixthMoment_power_margin

-- Phases K/L/Q: the same-B0 firewall, the Balanced7 compiler, non-vacuity
#print axioms Erdos287.V20Compiler.highConductorCutoff_mono
#print axioms Erdos287.V20Compiler.comparisonAtCutoff_to_base
#print axioms Erdos287.V20Compiler.comparisonAtCutoff_not_automatic
#print axioms Erdos287.V20Compiler.comparison_cutoff_must_match
#print axioms Erdos287.V20Compiler.balancedSeven_of_v20_package
#print axioms Erdos287.V20Compiler.v20_package_cutoff_consistent
#print axioms Erdos287.V20Compiler.hhh_input_not_automatic_v20
#print axioms Erdos287.V20Compiler.sixthMoment_input_not_automatic_v20
#print axioms Erdos287.V20Compiler.comparison_not_automatic_v20
#print axioms Erdos287.V20Compiler.logVar_cannot_construct_hhh
#print axioms Erdos287.V20Compiler.balancedSeven_compiler_cannot_construct_comparison

-- The ledger itself
#print axioms Erdos287.V20Status.controlling_analytic_residual_unique
#print axioms Erdos287.V20Status.sixthMoment_not_controlling
#print axioms Erdos287.V20Status.logVar_reduced_not_proved
#print axioms Erdos287.V20Status.capacity_firewalls_are_not_proofs
#print axioms Erdos287.V20Status.children_are_conditional
#print axioms Erdos287.V20Status.comparison_source_open
#print axioms Erdos287.V20Status.terminal_nodes_open

end AxiomAudit

end V20Audit
end Erdos287
