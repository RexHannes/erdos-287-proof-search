import RequestProject.Erdos287.Anchored.Reconciliation

/-!
# Anchored route — axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Every principal theorem of the anchored namespace is checked here with `#print axioms`.  No
custom axiom, `sorry`, `admit`, `native_decide`, `unsafe`, `opaque` or `@[implemented_by]`
occurs anywhere in this namespace; the only axioms reported are Lean's standard
`propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos287
namespace Anchored

#print axioms Erdos287.Anchored.one_le_padicValRat_iff_dvd_num
#print axioms Erdos287.Anchored.anchoredFeasible_iff_fingerprint
#print axioms Erdos287.Anchored.layer_primePower_iff
#print axioms Erdos287.Anchored.layer_primePower_iff_int
#print axioms Erdos287.Anchored.anchoredFeasible_iff_layer_primePower
#print axioms Erdos287.Anchored.layer_retains_p_dvd_cofactor
#print axioms Erdos287.Anchored.layerAllows_iff
#print axioms Erdos287.Anchored.ContactCSP.sat_iff_satB
#print axioms Erdos287.Anchored.ContactCSP.sat_elimLeaf_iff
#print axioms Erdos287.Anchored.ContactCSP.forest_decision
#print axioms Erdos287.Anchored.transfer_spec
#print axioms Erdos287.Anchored.pathCSP_sat_iff
#print axioms Erdos287.Anchored.cycleCSP_sat_iff
#print axioms Erdos287.Anchored.ContactCSP.excess_elimLeaf
#print axioms Erdos287.Anchored.ContactCSP.exists_peel_to_leafless
#print axioms Erdos287.Anchored.anchored_contact_endpoint
#print axioms Erdos287.Anchored.branchingKernelRejection_unconditional_false
#print axioms Erdos287.Anchored.padicValRat_recipSum_iff_zmod_inv_sum
#print axioms Erdos287.Anchored.topLayer_anchoredFeasible
#print axioms Erdos287.Anchored.counterexample_cofactorNum_eq_lcmOf
#print axioms Erdos287.Anchored.anchored_finite_frontier_unchanged
#print axioms Erdos287.Anchored.anchored_open_frontier

end Anchored
end Erdos287
