import RequestProject.Erdos287.ResearchBankV18.CharacterExpansion
import RequestProject.Erdos287.ResearchBankV18.ColourConductor
import RequestProject.Erdos287.ResearchBankV18.Ledger
import RequestProject.Erdos287.ResearchBankV18.NegativeControls
import RequestProject.Erdos287.ResearchBankV18.PostCenteringTransfer
import RequestProject.Erdos287.ResearchBankV18.ProviderInterfaces
import RequestProject.Erdos287.ResearchBankV18.ReciprocalMonomial
import RequestProject.Erdos287.ResearchBankV18.ScalarVariation

/-!
# Erdős #287 — Research Bank V18: axiom audit

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`#print axioms` for every theorem of Research Bank V18 (55 theorems).  Expected output:
only `propext`, `Classical.choice`, `Quot.sound` (or subsets).
-/

#print axioms Erdos287.ResearchBankV18.CharacterExpansion.totient_ne_zero
#print axioms Erdos287.ResearchBankV18.CharacterExpansion.expansion
#print axioms Erdos287.ResearchBankV18.CharacterExpansion.char_norm_le_one
#print axioms Erdos287.ResearchBankV18.CharacterExpansion.monomial_separation
#print axioms Erdos287.ResearchBankV18.CharacterExpansion.one_family_for_all_m
#print axioms Erdos287.ResearchBankV18.CharacterExpansion.separated_norm_le
#print axioms Erdos287.ResearchBankV18.CharacterExpansion.coef_shift
#print axioms Erdos287.ResearchBankV18.ColourConductor.e_add
#print axioms Erdos287.ResearchBankV18.ColourConductor.e_mul_self
#print axioms Erdos287.ResearchBankV18.ColourConductor.e_periodic
#print axioms Erdos287.ResearchBankV18.ColourConductor.e_congr
#print axioms Erdos287.ResearchBankV18.ColourConductor.e_scale
#print axioms Erdos287.ResearchBankV18.ColourConductor.e_one
#print axioms Erdos287.ResearchBankV18.ColourConductor.inverse_reduces
#print axioms Erdos287.ResearchBankV18.ColourConductor.colour_conductor_reduction
#print axioms Erdos287.ResearchBankV18.ColourConductor.colour_conductor_E_one
#print axioms Erdos287.ResearchBankV18.ColourConductor.nonunit_fixture
#print axioms Erdos287.ResearchBankV18.Ledger.v18_preserves_v17_ledger
#print axioms Erdos287.ResearchBankV18.Ledger.v18_erdos287_open
#print axioms Erdos287.ResearchBankV18.NegativeControls.residue_cell_strictly_weaker
#print axioms Erdos287.ResearchBankV18.NegativeControls.residue_cell_unbounded_in_m
#print axioms Erdos287.ResearchBankV18.NegativeControls.E_cost_le_D_cost
#print axioms Erdos287.ResearchBankV18.PostCenteringTransfer.bilin_left
#print axioms Erdos287.ResearchBankV18.PostCenteringTransfer.bilin_right
#print axioms Erdos287.ResearchBankV18.PostCenteringTransfer.trilin_bilin
#print axioms Erdos287.ResearchBankV18.PostCenteringTransfer.trilin_right
#print axioms Erdos287.ResearchBankV18.PostCenteringTransfer.split4
#print axioms Erdos287.ResearchBankV18.PostCenteringTransfer.multiplier_transfer
#print axioms Erdos287.ResearchBankV18.PostCenteringTransfer.multiplier_transfer_second
#print axioms Erdos287.ResearchBankV18.PostCenteringTransfer.pos_part_unit
#print axioms Erdos287.ResearchBankV18.PostCenteringTransfer.neg_part_unit
#print axioms Erdos287.ResearchBankV18.PostCenteringTransfer.decomp
#print axioms Erdos287.ResearchBankV18.PostCenteringTransfer.polarize_one
#print axioms Erdos287.ResearchBankV18.PostCenteringTransfer.polarize_two
#print axioms Erdos287.ResearchBankV18.PostCenteringTransfer.polarize_three
#print axioms Erdos287.ResearchBankV18.ProviderInterfaces.first_provider_falsifiable
#print axioms Erdos287.ResearchBankV18.ReciprocalMonomial.val_mul_modEq
#print axioms Erdos287.ResearchBankV18.ReciprocalMonomial.recipPhase_shift
#print axioms Erdos287.ResearchBankV18.ReciprocalMonomial.reciprocal_monomial_separation
#print axioms Erdos287.ResearchBankV18.ReciprocalMonomial.f0_bounded
#print axioms Erdos287.ResearchBankV18.ReciprocalMonomial.reciprocal_bound_by_variation
#print axioms Erdos287.ResearchBankV18.ScalarVariation.Mp_two
#print axioms Erdos287.ResearchBankV18.ScalarVariation.Mp_nonneg
#print axioms Erdos287.ResearchBankV18.ScalarVariation.Mp_le_sqrt
#print axioms Erdos287.ResearchBankV18.ScalarVariation.Mp_sq_le
#print axioms Erdos287.ResearchBankV18.ScalarVariation.Mp_cube_le
#print axioms Erdos287.ResearchBankV18.ScalarVariation.prod_Mp_cube_le
#print axioms Erdos287.ResearchBankV18.ScalarVariation.crt_phase_split
#print axioms Erdos287.ResearchBankV18.ScalarVariation.sum_units_eq
#print axioms Erdos287.ResearchBankV18.ScalarVariation.stdAddChar_eq_e
#print axioms Erdos287.ResearchBankV18.ScalarVariation.principal_sum
#print axioms Erdos287.ResearchBankV18.ScalarVariation.totient_real
#print axioms Erdos287.ResearchBankV18.ScalarVariation.principal_coef_norm
#print axioms Erdos287.ResearchBankV18.ScalarVariation.card_characters
#print axioms Erdos287.ResearchBankV18.ScalarVariation.local_variation_le
