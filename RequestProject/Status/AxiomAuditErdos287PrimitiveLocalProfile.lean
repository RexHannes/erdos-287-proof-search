import Mathlib
import RequestProject.Status.CurrentStatusErdos287PrimitiveLocalProfile

/-!
# Trust audit — Erdős #287, PRIMITIVE-LOCALPROFILE Δ

`#print axioms` over every principal declaration added by this pass.  Expected output for
each: a subset of `propext`, `Classical.choice`, `Quot.sound`.

The new files contain no `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or
`@[implemented_by]`, and neither analytic socket of this pass (`ShortLiftEulerAnalyticInput`,
`PrimitiveLocalProfileGramInput`) has an inhabitant anywhere in the repository.
-/

namespace Erdos287
namespace PrimitiveLocalProfileAudit

/-! ## §A  Primitive `t` Ramanujan algebra -/

#print axioms Erdos287.PrimitiveRamanujan.phase_pow
#print axioms Erdos287.PrimitiveRamanujan.phase_eq_one_iff
#print axioms Erdos287.PrimitiveRamanujan.full_phase_sum
#print axioms Erdos287.PrimitiveRamanujan.ramanujan_congr
#print axioms Erdos287.PrimitiveRamanujan.coprime_div_of_squarefree
#print axioms Erdos287.PrimitiveRamanujan.multiples_image
#print axioms Erdos287.PrimitiveRamanujan.ramanujan_eq_divisor_sum
#print axioms Erdos287.PrimitiveRamanujan.ramanujan_unit_mul
#print axioms Erdos287.PrimitiveRamanujan.ramanujan_unit_shift
#print axioms Erdos287.PrimitiveRamanujan.moebius_mul_moebius_div
#print axioms Erdos287.PrimitiveRamanujan.ramanujan_moebius_normalForm

/-! ## §B  Reassembly representation loop -/

#print axioms Erdos287.PrimitiveReassembly.moebius_properDivisors_sum
#print axioms Erdos287.PrimitiveReassembly.reassemblyBranch_of_coprime
#print axioms Erdos287.PrimitiveReassembly.reassemblyBranch_one
#print axioms Erdos287.PrimitiveReassembly.reassemblyBranch_eq_zero
#print axioms Erdos287.PrimitiveReassembly.primitive_ramanujan_reassembly

/-! ## §C  Short-lift local profile -/

#print axioms Erdos287.ShortLift.mProfile_add
#print axioms Erdos287.ShortLift.mProfile_smul
#print axioms Erdos287.ShortLift.mProfile_zero_weight
#print axioms Erdos287.ShortLift.isMultiplicative_coprimeInvWeight
#print axioms Erdos287.ShortLift.mProfileDivisor_euler_product
#print axioms Erdos287.ShortLift.shortLift_euler_collapse_finite
#print axioms Erdos287.ShortLift.shortLift_euler_collapse_of_input

/-! ## §D  Primitive `D`-frequency multiplicity -/

#print axioms Erdos287.PrimitiveD.dLine_solution_form
#print axioms Erdos287.PrimitiveD.dSolutionSet_card_le_g0
#print axioms Erdos287.PrimitiveD.dSolutionSet_card_le

/-! ## §E  Farey near-collision -/

#print axioms Erdos287.PrimitiveFarey.lcm_of_coprime_cofactors
#print axioms Erdos287.PrimitiveFarey.farey_near_collision_D_bound
#print axioms Erdos287.PrimitiveFarey.farey_near_collision_lcm_bound
#print axioms Erdos287.PrimitiveFarey.nearCollisionSet_card_le

/-! ## §F  The current source socket -/

#print axioms Erdos287.PrimitiveLocalProfile.localProfile_is_the_repository_mProfile
#print axioms Erdos287.PrimitiveLocalProfile.exists_valid_config
#print axioms Erdos287.PrimitiveLocalProfile.primitiveLocalProfileGram_compiler
#print axioms Erdos287.PrimitiveLocalProfile.primitiveLocalProfileGram_not_automatic
#print axioms Erdos287.PrimitiveLocalProfile.analytic_target_exponent

/-! ## §G  Status layer -/

#print axioms Erdos287.PrimitiveLocalProfileStatus.no_closed_rows
#print axioms Erdos287.PrimitiveLocalProfileStatus.erdos287_open
#print axioms Erdos287.PrimitiveLocalProfileStatus.uniform_k0_open_fcl_not_reached
#print axioms Erdos287.PrimitiveLocalProfileStatus.shortLiftGram_superseded_not_false
#print axioms Erdos287.PrimitiveLocalProfileStatus.localProfileGram_is_first_exact_mainline_residual
#print axioms Erdos287.PrimitiveLocalProfileStatus.exact_rows_are_theorems
#print axioms Erdos287.PrimitiveLocalProfileStatus.analytic_rows_are_uninhabited
#print axioms Erdos287.PrimitiveLocalProfileStatus.historical_block20_status_preserved

end PrimitiveLocalProfileAudit
end Erdos287
