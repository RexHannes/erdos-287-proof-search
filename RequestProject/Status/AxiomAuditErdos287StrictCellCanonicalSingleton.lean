import RequestProject.Status.CurrentStatusErdos287StrictCellCanonicalSingleton

/-!
# Axiom audit — Erdős #287 strict-cell canonical-singleton frontier

`#print axioms` for every principal new theorem of this delta.  The build log must show only
`propext`, `Classical.choice`, `Quot.sound` (or nothing at all); in particular no `sorryAx`
and no user axiom.
-/

namespace Erdos287
namespace StrictCellAudit

open Erdos287.StrictCellSingleton
open Erdos287.StrictCellBridge
open Erdos287.StrictCellSingletonStatus

/-! ## §1  The pushforward and its countermodel -/

#print axioms OmegaSharp_unitWeight
#print axioms OmegaSharp_eq_zero_of_not_mem_image
#print axioms mem_omegaSharpFibre_iff
#print axioms countermodelCert_packet
#print axioms countermodel_fibre_card
#print axioms omegaSharp_eq_seven
#print axioms omegaSharp_one_not_automatic

/-! ## §2  Strict-cell hypotheses, `k = 0`, `J = ∅`, no `d`-variables -/

#print axioms strictCell_k_zero
#print axioms strictCell_J_empty
#print axioms strictCell_packetNormalization
#print axioms strictCellHypotheses_inhabited
#print axioms dIndex_eq_empty
#print axioms dIndex_card_zero
#print axioms dIndex_not_automatically_empty

/-! ## §3  Ford coordinates, branches, coordinate kinds -/

#print axioms ford_coordCount_eq_nine
#print axioms slotCount_le_four
#print axioms rankCount_ge_five
#print axioms fordBranches_card
#print axioms mem_fordBranches
#print axioms physicalPrimeCoords_card
#print axioms terminalUnitCoords_card
#print axioms coordKind_partition

/-! ## §4  Canonical singleton, complement, `H^*` -/

#print axioms compl_nonempty_of_card_le_three
#print axioms canonicalSingleton_not_mem
#print axioms canonicalSingleton_le
#print axioms canonicalSingleton_unique
#print axioms complementDepth_eq_six
#print axioms canonicalSingleton_not_mem_complement
#print axioms singleton_union_complement
#print axioms balancedSeven_divisorDepth
#print axioms hStar_eq_neg_twenty
#print axioms hStar_eq_balancedSevenLowSum
#print axioms hStar_constant

/-! ## §5  The physical `k = 0` (7.20) package -/

#print axioms physicalK0_of_strictCell
#print axioms perronContourCount_eq_zero

/-! ## §6  Exact mass, windows, energies, counterguard -/

#print axioms cellVectors_card
#print axioms omegaSharp_total_mass
#print axioms productWeight_total_mass
#print axioms singleton_mem_window
#print axioms complement_pushforward_bounds
#print axioms pushforward_bounds
#print axioms prod_testVector
#print axioms diagonalWeight_testVector
#print axioms weight_not_product_separable
#print axioms finite_cauchy_schwarz
#print axioms productEnergy_factorises
#print axioms cell_cauchy_productEnergy

/-! ## §7  The bridge, the kernel factorisation and the Type-II input -/

#print axioms kernel_not_automatically_separable
#print axioms bridge_not_automatic
#print axioms bridge_kernel_factorisation
#print axioms kernel_canonical_factor_eq
#print axioms bridge_complement_depth_eq_six
#print axioms bridge_physicalK0
#print axioms bridge_H_eq_neg_twenty
#print axioms bridge_perronContourCount_zero
#print axioms bridge_pointwise
#print axioms bridge_total_mass
#print axioms bridge_singleton_window
#print axioms typeII_input_not_automatic
#print axioms bridge_is_an_input_not_a_theorem

/-! ## §8  The status layer -/

#print axioms erdos287_open
#print axioms ford723Census_superseded
#print axioms superseded_ne_retracted
#print axioms packetCensus_conditional
#print axioms bridge_open
#print axioms typeII_open
#print axioms unique_kernelProved_row
#print axioms backing_omegaSharp_not_one
#print axioms backing_coordCount
#print axioms backing_sixtyFour_branches
#print axioms backing_seven_two
#print axioms backing_hStar
#print axioms backing_complement_depth
#print axioms backing_no_d_no_contour
#print axioms backing_k_zero_J_empty
#print axioms backing_canonical_singleton
#print axioms backing_productEnergy
#print axioms census_is_an_implication
#print axioms backing_bridge_open
#print axioms backing_typeII_open
#print axioms backing_separation_counterguards
#print axioms no_analytic_typeII_claimed
#print axioms erdos287_not_closed

end StrictCellAudit
end Erdos287
