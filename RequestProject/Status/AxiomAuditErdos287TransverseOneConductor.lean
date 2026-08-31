import Mathlib
import RequestProject.Status.CurrentStatusErdos287TransverseBezoutSingleCarrier

/-!
# Axiom audit — Erdős #287, transverse one-conductor Δ

`#print axioms` for every declaration of this append-only delta.

Allowed inherited axioms only:

```
propext, Classical.choice, Quot.sound
```

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `implemented_by` occurs as
a code construct in any module of this delta; those words appear only inside docstring prose.
Decidable ledger and finite arithmetic facts are discharged with `decide +kernel` or `norm_num`.

The conditional statements (`transverseQCGroupedUnitary_of_productEnergy`,
`denseQC_closed_of_unitary_margin`) depend only on their explicitly named hypotheses, and each
hypothesis shell is proved non-automatic, so nothing is silently discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace TransverseOneConductorAudit

/-! ## Transverse source factorisation and reduced conductors -/

#print axioms Erdos287.TransverseReducedConductor.TransversePacket
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.E
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.R
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.B0
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.M0
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.E_mul_a1
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.R_mul_c2
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.E_pos
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.R_pos
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.B0_pos
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.M0_pos
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.qC
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.RSource
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.delta2
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.deltaE
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.deltaB
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.twoCirc
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.ECirc
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.BCirc
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.delta2_dvd_two
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.deltaE_dvd_E
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.deltaB_dvd_B0
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.twoCirc_mul_delta2
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.ECirc_mul_deltaE
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.BCirc_mul_deltaB
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.twoCirc_pos
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.ECirc_pos
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.BCirc_pos
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.qBar
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.qm
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.RHat
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.qBar_pos
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.RHat_pos
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.RHat_eq
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.qBar_mul_deltas
#print axioms Erdos287.TransverseReducedConductor.TransversePacket.qBar_dvd_qC
#print axioms Erdos287.TransverseReducedConductor.primed_packet_symmetric
#print axioms Erdos287.TransverseReducedConductor.lcm_eq_mul_div_gcd
#print axioms Erdos287.TransverseReducedConductor.QStar
#print axioms Erdos287.TransverseReducedConductor.dStar
#print axioms Erdos287.TransverseReducedConductor.QStarRed
#print axioms Erdos287.TransverseReducedConductor.QStar_pos
#print axioms Erdos287.TransverseReducedConductor.dStar_dvd_QStar
#print axioms Erdos287.TransverseReducedConductor.QStarRed_mul_dStar
#print axioms Erdos287.TransverseReducedConductor.QStarRed_exact_normal_form
#print axioms Erdos287.TransverseReducedConductor.QStarRed_eq_div
#print axioms Erdos287.TransverseReducedConductor.carrierClass
#print axioms Erdos287.TransverseReducedConductor.carrierClass_table
#print axioms Erdos287.TransverseReducedConductor.carrierClass_is_metadata
#print axioms Erdos287.TransverseReducedConductor.Rcarrier_harmonic_square_bound

/-! ## One-conductor reciprocity -/

#print axioms Erdos287.TransverseOneConductor.intGcd_congr
#print axioms Erdos287.TransverseOneConductor.exists_inverse_of_coprime
#print axioms Erdos287.TransverseOneConductor.transverseGammaInt
#print axioms Erdos287.TransverseOneConductor.transverseGammaInt_modEq_m
#print axioms Erdos287.TransverseOneConductor.transverseGammaInt_modEq_r
#print axioms Erdos287.TransverseOneConductor.transverseGamma
#print axioms Erdos287.TransverseOneConductor.transverseGamma_mod_m
#print axioms Erdos287.TransverseOneConductor.transverseGamma_mod_r
#print axioms Erdos287.TransverseOneConductor.reducedPhase
#print axioms Erdos287.TransverseOneConductor.reducedPhase_norm
#print axioms Erdos287.TransverseOneConductor.reducedPhase_arithmetic_factor
#print axioms Erdos287.TransverseOneConductor.transverseGamma_test_r5_m3

/-! ## Gamma gcd normal form and reduction -/

#print axioms Erdos287.TransverseGammaReduction.gP
#print axioms Erdos287.TransverseGammaReduction.gP_pos
#print axioms Erdos287.TransverseGammaReduction.gP_dvd_r
#print axioms Erdos287.TransverseGammaReduction.gP_dvd_rm
#print axioms Erdos287.TransverseGammaReduction.transverseGamma_gcd_eq
#print axioms Erdos287.TransverseGammaReduction.gP_dvd_gamma
#print axioms Erdos287.TransverseGammaReduction.mP
#print axioms Erdos287.TransverseGammaReduction.transverseGammaRed
#print axioms Erdos287.TransverseGammaReduction.mP_mul_gP
#print axioms Erdos287.TransverseGammaReduction.mP_pos
#print axioms Erdos287.TransverseGammaReduction.transverseGammaRed_mul_gP
#print axioms Erdos287.TransverseGammaReduction.transverseGammaRed_coprime
#print axioms Erdos287.TransverseGammaReduction.transverseGammaRed_isUnit
#print axioms Erdos287.TransverseGammaReduction.OneConductorData
#print axioms Erdos287.TransverseGammaReduction.OneConductorData.Gamma
#print axioms Erdos287.TransverseGammaReduction.OneConductorData.gcdP
#print axioms Erdos287.TransverseGammaReduction.OneConductorData.modP
#print axioms Erdos287.TransverseGammaReduction.OneConductorData.GammaRed
#print axioms Erdos287.TransverseGammaReduction.OneConductorData.modP_pos
#print axioms Erdos287.TransverseGammaReduction.OneConductorData.gcd_normal_form
#print axioms Erdos287.TransverseGammaReduction.OneConductorData.gammaRed_coprime
#print axioms Erdos287.TransverseGammaReduction.OneConductorData.gammaRed_isUnit
#print axioms Erdos287.TransverseGammaReduction.OneConductorData.modP_neZero
#print axioms Erdos287.TransverseGammaReduction.gammaReduction_test_r10_m3

/-! ## qC unitary Fourier compiler (reuse only) -/

#print axioms Erdos287.TransverseQCUnitary.inv_mul_factorisation_zmod
#print axioms Erdos287.TransverseQCUnitary.natCast_isUnit_of_coprime
#print axioms Erdos287.TransverseQCUnitary.inv_mul_factorisation_zmod_nat
#print axioms Erdos287.TransverseQCUnitary.inv_mul_factorisation_test
#print axioms Erdos287.TransverseQCUnitary.transverseQCUnitaryFourier_bound
#print axioms Erdos287.TransverseQCUnitary.transverseQCUnitaryFourier_l2_bound
#print axioms Erdos287.TransverseQCUnitary.QBarPartition
#print axioms Erdos287.TransverseQCUnitary.qBarPartition_trivial
#print axioms Erdos287.TransverseQCUnitary.qBarPartition_nontrivial_not_automatic
#print axioms Erdos287.TransverseQCUnitary.transverseQCGroupedUnitary_of_productEnergy
#print axioms Erdos287.TransverseQCUnitary.transverseQCUnitary_omegaH_blind

/-! ## Dense-qC conditional interface -/

#print axioms Erdos287.TransverseDenseQC.DenseQCAdmissible
#print axioms Erdos287.TransverseDenseQC.denseQCAdmissible_implies_dense_inequality
#print axioms Erdos287.TransverseDenseQC.denseQCAdmissible_not_automatic
#print axioms Erdos287.TransverseDenseQC.denseQC_closed_of_unitary_margin
#print axioms Erdos287.TransverseDenseQC.denseQC_margin_not_automatic
#print axioms Erdos287.TransverseDenseQC.denseQC_admissibility_does_not_give_the_bound

/-! ## Status layer (metadata) -/

#print axioms Erdos287.TransverseBezoutStatus.bezoutLedger
#print axioms Erdos287.TransverseBezoutStatus.threefactorTransverseOneConductorReciprocityStatus
#print axioms Erdos287.TransverseBezoutStatus.transverseOneConductorStatus
#print axioms Erdos287.TransverseBezoutStatus.transverseQCUnitaryStatus
#print axioms Erdos287.TransverseBezoutStatus.transverseDenseQCStatus
#print axioms Erdos287.TransverseBezoutStatus.transverseCriticalBezoutSingleCarrierStatus
#print axioms Erdos287.TransverseBezoutStatus.carrierFactorizationPairExistenceStatus
#print axioms Erdos287.TransverseBezoutStatus.criticalPolytopeStatus
#print axioms Erdos287.TransverseBezoutStatus.naiveFullCRTDFTStatus
#print axioms Erdos287.TransverseBezoutStatus.c0Status
#print axioms Erdos287.TransverseBezoutStatus.exactProductCollisionStatus
#print axioms Erdos287.TransverseBezoutStatus.doubleTypeIIStatus
#print axioms Erdos287.TransverseBezoutStatus.bDiagonalStatus
#print axioms Erdos287.TransverseBezoutStatus.transverseStatus
#print axioms Erdos287.TransverseBezoutStatus.erdos287Status
#print axioms Erdos287.TransverseBezoutStatus.new_kernel_rows
#print axioms Erdos287.TransverseBezoutStatus.transverse_bank_rows
#print axioms Erdos287.TransverseBezoutStatus.oneConductor_status_label
#print axioms Erdos287.TransverseBezoutStatus.criticalBezout_is_first_frontier
#print axioms Erdos287.TransverseBezoutStatus.criticalPolytope_open
#print axioms Erdos287.TransverseBezoutStatus.naive_full_crt_dft_retracted
#print axioms Erdos287.TransverseBezoutStatus.conditionality_firewall
#print axioms Erdos287.TransverseBezoutStatus.c0_still_conditional
#print axioms Erdos287.TransverseBezoutStatus.analytic_branch_rows
#print axioms Erdos287.TransverseBezoutStatus.bdiagonal_firewall
#print axioms Erdos287.TransverseBezoutStatus.no_double_spending_after_oneConductor
#print axioms Erdos287.TransverseBezoutStatus.erdos287_still_open
#print axioms Erdos287.TransverseBezoutStatus.previous_transverse_ledger_preserved
#print axioms Erdos287.TransverseBezoutStatus.c0_ledger_still_preserved_after_oneConductor
#print axioms Erdos287.TransverseBezoutStatus.criticalSurvivor_conditions_are_metadata
end TransverseOneConductorAudit
end Erdos287
