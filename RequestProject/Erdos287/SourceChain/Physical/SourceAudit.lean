import RequestProject.Erdos287.SourceChain.Physical.Bridge
import RequestProject.Erdos287.SourceChain.Physical.TypeII.Instance

/-!
# Erdős #287 — physical source completion: axiom audit and negative controls

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

Each `#print axioms` line must report only `[propext, Classical.choice, Quot.sound]` (or a
subset): no `sorryAx`, no `Lean.ofReduceBool`, no custom axiom.
-/

open Erdos287.Physical

/-! ### Task A — scalar coefficient -/
#print axioms Erdos287.Physical.Sieve.ScalarParams.lamLowPlus_sum_ge
#print axioms Erdos287.Physical.Sieve.ScalarParams.lamLowMinus_sum_le
#print axioms Erdos287.Physical.Sieve.ScalarParams.kappa_level
#print axioms Erdos287.Physical.Sieve.ScalarParams.sum_Bcoef_eq_hw
#print axioms Erdos287.Physical.Sieve.ScalarParams.ellX_eq_setForm
#print axioms Erdos287.Physical.Sieve.ScalarParams.ellX_J0_sector
#print axioms Erdos287.Physical.Sieve.ScalarParams.ellX_support
#print axioms Erdos287.Physical.Sieve.ScalarParams.ellX_level
#print axioms Erdos287.Physical.Sieve.ScalarParams.UX_eq_parity_sum
#print axioms Erdos287.Physical.Sieve.ScalarParams.UX_nonneg
#print axioms Erdos287.Physical.Sieve.ScalarParams.UX_majorant
#print axioms Erdos287.Physical.Sieve.ScalarParams.UX_ge_one_of_prime
#print axioms Erdos287.Physical.Sieve.ScalarParams.abs_ellX_le

/-! ### Task B — Type-II source -/
#print axioms Erdos287.Physical.TypeII.heathBrown
#print axioms Erdos287.Physical.TypeII.heathBrown_three
#print axioms Erdos287.Physical.TypeII.heathBrown_maynard_range
#print axioms Erdos287.Physical.TypeII.hbTerm_eq_sum_cells
#print axioms Erdos287.Physical.TypeII.cellSeq_eq_alpha_mul_beta
#print axioms Erdos287.Physical.TypeII.abs_alpha_le
#print axioms Erdos287.Physical.TypeII.alpha_support
#print axioms Erdos287.Physical.TypeII.abs_betaSeq_le
#print axioms Erdos287.Physical.TypeII.typeII_split_Z
#print axioms Erdos287.Physical.TypeII.OBData.T_sq_le
#print axioms Erdos287.Physical.TypeII.OBData.V_expand
#print axioms Erdos287.Physical.TypeII.base_congruence
#print axioms Erdos287.Physical.TypeII.OBData.source_eq_T
#print axioms Erdos287.Physical.TypeII.physCoef_abs_le
#print axioms Erdos287.Physical.TypeII.physCoef_coprime
#print axioms Erdos287.Physical.TypeII.physCoef_reassemble

/-! ### Task C — bridges -/
#print axioms Erdos287.Physical.PhysData.majorizedMoment_eq_pairSum
#print axioms Erdos287.Physical.PhysData.pairSum_eq_packets_pos
#print axioms Erdos287.Physical.PhysData.majorizedMoment_eq_packets
#print axioms Erdos287.Physical.PhysData.twoPrimeMoment_le_packets

/-! ### Negative controls -/

-- Maynard's printed sign `(-1)^j` in Lemma 5.3 is refuted (the correct sign is
-- `(-1)^{j+1}`).
#print axioms Erdos287.Physical.TypeII.maynard_printed_sign_false

/-- The multiplicative split `U_{lr} = U_l U_r` (used by `typeII_split_Z`) genuinely needs
`(l, r) = 1`: it fails at `l = r = 2`. -/
theorem Erdos287.Physical.TypeII.Uz_mul_needs_coprime :
    Erdos287.Physical.TypeII.Uz (2 * 2) 1 ≠
      Erdos287.Physical.TypeII.Uz 2 1 * Erdos287.Physical.TypeII.Uz 2 1 := by
  unfold Erdos287.Physical.TypeII.Uz
  have h4 : Nat.totient 4 = 2 := by decide
  simp [h4]

#print axioms Erdos287.Physical.TypeII.Uz_mul_needs_coprime
