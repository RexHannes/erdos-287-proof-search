import RequestProject.Erdos287.AnchoredV2.Reconciliation

/-!
# Anchored V2 — axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Every principal exported theorem of the Anchored V2 namespace is checked here with
`#print axioms`.  No custom axiom, `sorry`, `admit`, `native_decide`, `unsafe`, `opaque` or
`@[implemented_by]` occurs anywhere in this namespace; the only axioms reported are Lean's
standard `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos287
namespace AnchoredV2

-- feedback-edge reduction
#print axioms Erdos287.AnchoredV2.sat_iff_exists_branch
#print axioms Erdos287.AnchoredV2.branch_count
#print axioms Erdos287.AnchoredV2.feedbackSet_card
#print axioms Erdos287.AnchoredV2.anchored_forest_branches
#print axioms Erdos287.AnchoredV2.beta_two_four_tests

-- block-cut and cactus
#print axioms Erdos287.AnchoredV2.sat_split_iff
#print axioms Erdos287.AnchoredV2.sat_split_single_iff
#print axioms Erdos287.AnchoredV2.cactus_star_sat_iff
#print axioms Erdos287.AnchoredV2.msg2_pathChild

-- affine normal form
#print axioms Erdos287.AnchoredV2.AffineTreeData.famLabel_satisfiesTree
#print axioms Erdos287.AnchoredV2.AffineTreeData.eq_famLabel_of_satisfiesTree
#print axioms Erdos287.AnchoredV2.AffineTreeData.nonTree_dichotomy
#print axioms Erdos287.AnchoredV2.AffineTreeData.fullyBalanced_one_parameter
#print axioms Erdos287.AnchoredV2.AffineTreeData.integral_root_progression
#print axioms Erdos287.AnchoredV2.AffineTreeData.integral_progression_sound

-- theta firewall
#print axioms Erdos287.AnchoredV2.thetaBalancedRejection_false

-- tracked kernel
#print axioms Erdos287.AnchoredV2.TrackedPrimeKernel.feasible_of_refines
#print axioms Erdos287.AnchoredV2.TrackedPrimeKernel.contact_sat_of_feasible

-- unit subset-sum and coupled charge
#print axioms Erdos287.AnchoredV2.exists_subset_sum_eq
#print axioms Erdos287.AnchoredV2.coupled_subset_sum

-- finite coupled extension
#print axioms Erdos287.AnchoredV2.finite_coupled_extension
#print axioms Erdos287.AnchoredV2.feasible_of_fullTrackedSolution
#print axioms Erdos287.AnchoredV2.fullTrackedSolution_iff_feasible
#print axioms Erdos287.AnchoredV2.coupledBatchSupply_of_fixedPower

-- capacity
#print axioms Erdos287.AnchoredV2.PortSystem.cap_mono
#print axioms Erdos287.AnchoredV2.PortSystem.capacity_sound
#print axioms Erdos287.AnchoredV2.PortSystem.slack_mono
#print axioms Erdos287.AnchoredV2.NegativeCapacityCertificate.not_feasible
#print axioms Erdos287.AnchoredV2.capacity_incompleteness

-- Level 2
#print axioms Erdos287.AnchoredV2.PortSystem.level2_of_feasible
#print axioms Erdos287.AnchoredV2.PortSystem.not_feasible_of_not_level2

-- bridges to the actual anchored kernels and the refinement of the V1 owner
#print axioms Erdos287.AnchoredV2.feasible_of_sat
#print axioms Erdos287.AnchoredV2.negativeCapacity_rejects_anchored
#print axioms Erdos287.AnchoredV2.level2_rejects_anchored
#print axioms Erdos287.AnchoredV2.negativeCapacity_rejects_trackedKernel
#print axioms Erdos287.AnchoredV2.level2_rejects_trackedKernel
#print axioms Erdos287.AnchoredV2.branchingKernelRejection_of_uniformNegativeCapacity
#print axioms Erdos287.AnchoredV2.branchingKernelRejection_of_uniformLevel2Rejection

-- ledgers
#print axioms Erdos287.AnchoredV2.v1_owner_refined
#print axioms Erdos287.AnchoredV2.v2_routes_preserved
#print axioms Erdos287.AnchoredV2.v2_finite_frontier_unchanged
#print axioms Erdos287.AnchoredV2.v2_open_frontier

end AnchoredV2
end Erdos287
