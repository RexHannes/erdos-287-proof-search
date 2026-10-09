import RequestProject.Erdos287.ResearchBankV6.UpperGapCarry
import RequestProject.Erdos287.ResearchBankV6.SupportDisjointness
import RequestProject.Erdos287.ResearchBankV6.UpperGapContact
import RequestProject.Erdos287.ResearchBankV6.ContactTarget
import RequestProject.Erdos287.ResearchBankV6.MiddleBand
import RequestProject.Erdos287.ResearchBankV6.OpenOwners
import RequestProject.Erdos287.ResearchBankV6.FullFrozen
import RequestProject.Erdos287.ResearchBankV6.Ledger

/-!
# Research Bank V6 — axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Every principal V6 theorem is audited here with `#print axioms`.  Only Lean's standard `propext`,
`Classical.choice` and `Quot.sound` may appear.

There is no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `opaque` or `@[implemented_by]`
anywhere in the V6 layer.  The only computational steps are the finite `decide` fixtures
(`contact_bound_sharp`, the counterfixture, and the decidable ledger checks); these are
kernel-reducible and are kept separate from the general mathematical theorems.
-/

namespace Erdos287
namespace ResearchBankV6

-- A.  Upper-gap carry kernel
#print axioms Erdos287.ResearchBankV6.UpperGap.lcmUpto_pos
#print axioms Erdos287.ResearchBankV6.UpperGap.dvd_lcmUpto
#print axioms Erdos287.ResearchBankV6.UpperGap.allowedCofactors_window
#print axioms Erdos287.ResearchBankV6.UpperGap.allowedCofactors_dvd_lcm
#print axioms Erdos287.ResearchBankV6.UpperGap.rowMass_eq_div
#print axioms Erdos287.ResearchBankV6.UpperGap.den_dvd_iff
#print axioms Erdos287.ResearchBankV6.UpperGap.prime_removed_iff_dvd_rowNumerator
#print axioms Erdos287.ResearchBankV6.UpperGap.rowMass_eq_carry_div
#print axioms Erdos287.ResearchBankV6.UpperGap.carry_height_aggregation

-- B.  Counterfixture (finite diagnostics, kept separate)
#print axioms Erdos287.ResearchBankV6.UpperGap.rowNumerator_range_substitution_counterfixture
#print axioms Erdos287.ResearchBankV6.UpperGap.rowMass_range_substitution_counterfixture

-- C.  Support disjointness
#print axioms Erdos287.ResearchBankV6.UpperGap.no_shared_denominator
#print axioms Erdos287.ResearchBankV6.UpperGap.rowSupport_disjoint
#print axioms Erdos287.ResearchBankV6.UpperGap.rowSupport_disjoint_of_sqrt_lt
#print axioms Erdos287.ResearchBankV6.UpperGap.rowSupports_pairwiseDisjoint
#print axioms Erdos287.ResearchBankV6.UpperGap.shared_support_does_not_give_independence

-- D.  Upper-gap contact relation
#print axioms Erdos287.ResearchBankV6.UpperGap.contact_coprime
#print axioms Erdos287.ResearchBankV6.UpperGap.rowContact_prime_ne
#print axioms Erdos287.ResearchBankV6.UpperGap.contactFibre_card_le
#print axioms Erdos287.ResearchBankV6.UpperGap.contact_bound_sharp
#print axioms Erdos287.ResearchBankV6.UpperGap.contact_count_not_globally_sparse
#print axioms Erdos287.ResearchBankV6.UpperGap.contact_partner_unique
#print axioms Erdos287.ResearchBankV6.UpperGap.rowContact_partner_unique
#print axioms Erdos287.ResearchBankV6.UpperGap.traceContacts_card_le

-- E.  Finite contact target and the (separate) asymptotic adapter
#print axioms Erdos287.ResearchBankV6.ContactTarget.squareMultiples_card
#print axioms Erdos287.ResearchBankV6.ContactTarget.card_le_of_charge
#print axioms Erdos287.ResearchBankV6.ContactTarget.contact_target_bound
#print axioms Erdos287.ResearchBankV6.ContactTarget.contact_target_bound_real
#print axioms Erdos287.ResearchBankV6.ContactTarget.balanced_scale
#print axioms Erdos287.ResearchBankV6.ContactTarget.contact_target_at_balanced_scale
#print axioms Erdos287.ResearchBankV6.ContactTarget.contact_cubeRoot_conditional

-- F.  Middle band (conditional on the uninhabited additive interface)
#print axioms Erdos287.ResearchBankV6.MiddleBand.restrictedSumset_covers
#print axioms Erdos287.ResearchBankV6.MiddleBand.middleRows_completable
#print axioms Erdos287.ResearchBankV6.MiddleBand.completion_preserves_trace
#print axioms Erdos287.ResearchBankV6.MiddleBand.completion_agrees_on_middle
#print axioms Erdos287.ResearchBankV6.MiddleBand.middleBand_sameTrace_conditional

-- G.  Open owners and their exact consequences
#print axioms Erdos287.ResearchBankV6.OpenOwners.aggregateMass_eq_active
#print axioms Erdos287.ResearchBankV6.OpenOwners.mass_single_term_of_support_one
#print axioms Erdos287.ResearchBankV6.OpenOwners.mass_den_dvd_of_granularity
#print axioms Erdos287.ResearchBankV6.OpenOwners.sum_in_lattice
#print axioms Erdos287.ResearchBankV6.OpenOwners.no_unit_mass_of_exactMassIntersection
#print axioms Erdos287.ResearchBankV6.OpenOwners.den_dvd_does_not_close
#print axioms Erdos287.ResearchBankV6.OpenOwners.den_dvd_not_sufficient

-- H.  FULL-FROZEN denominator entry
#print axioms Erdos287.ResearchBankV6.FullFrozen.row_disjoint_of_window_exclusion
#print axioms Erdos287.ResearchBankV6.FullFrozen.row_card_zero_of_window_exclusion

-- I.  Ledger, verdicts and the closure DAG
#print axioms Erdos287.ResearchBankV6.Ledger.ofV5_injective
#print axioms Erdos287.ResearchBankV6.Ledger.routes_pairwise_distinct
#print axioms Erdos287.ResearchBankV6.Ledger.no_closed_verdict
#print axioms Erdos287.ResearchBankV6.Ledger.erdos287_ownerOpen
#print axioms Erdos287.ResearchBankV6.Ledger.kernelBanked_iff_kernelProof
#print axioms Erdos287.ResearchBankV6.Ledger.nonKernel_rows_not_proved
#print axioms Erdos287.ResearchBankV6.Ledger.dag_edges_are_proved
#print axioms Erdos287.ResearchBankV6.Ledger.routes_not_claimed_equivalent
#print axioms Erdos287.ResearchBankV6.Ledger.ownerOpen_row_is_not_a_proof
#print axioms Erdos287.ResearchBankV6.Ledger.ledger_is_not_a_proof
#print axioms Erdos287.ResearchBankV6.Ledger.erdos287_not_closed_in_v6

end ResearchBankV6
end Erdos287
