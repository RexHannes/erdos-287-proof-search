import Mathlib
import RequestProject.Status.CurrentStatusErdos287C0SourceLift
import RequestProject.CurrentProgramme.Erdos287ReciprocalUnitaryFourier
import RequestProject.CurrentProgramme.Erdos287BalancedBUnitaryFourierCompiler
import RequestProject.CurrentProgramme.Erdos287AffineBilinearReciprocalNumerator
import RequestProject.CurrentProgramme.Erdos287C0PhysicalNormalisationInterface

/-!
# Append-only status layer — Erdős #287, C0 unitary-Fourier delta

This module is **append-only**.  The C0 source-lift ledger (`CurrentStatusErdos287C0SourceLift`)
and everything it imports are re-checked, not edited; `sourceLift_ledger_still_preserved`
records that its rows are unchanged.

```
C0 ANALYTIC CORE:
    CLOSED.

C0 PHYSICAL/FORMAL NORMALISATION:
    OPEN SOURCE PIN.

Therefore:
    C0 ANALYTICALLY CLOSED
    CONDITIONAL ON FORMAL NORMALISATION.
```

The bare phrase “C0 CLOSED” is deliberately **not** used, here or in the report.

Nothing in this file has any implication for mathematical truth: `ResearchStatus` is metadata.
The only kernel-proved rows are the finite Fourier/algebraic theorems of this delta.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace C0UnitaryFourierStatus

/-! ## §1  The research-status datatype (metadata only) -/

/-- Research status labels.  **No value of this type carries any implication of mathematical
truth**; only `kernelProved` rows correspond to theorems of this repository, and even then the
label is a record, not a proof. -/
inductive ResearchStatus
  /-- Backed by an unconditional, kernel-checked theorem of this repository. -/
  | kernelProved
  /-- Analytic research bank: closed on paper, not formalised. -/
  | analyticBanked
  /-- Conditional on a formal source pin that is not proved here. -/
  | conditionalSourcePin
  /-- Strictly reduced but still open. -/
  | strictReduction
  /-- Open. -/
  | open_
  /-- Superseded by a later architecture. -/
  | superseded
  /-- Permanently retracted architecture; must not be re-encoded. -/
  | retracted
  deriving DecidableEq, Fintype, Repr

/-! ## §2  Nodes of this delta -/

/-- Nodes of the C0 unitary-Fourier ledger. -/
inductive C0FourierNode
  /-- Finite reciprocal unitary Fourier Gram / bilinear bounds. -/
  | reciprocalUnitaryFourier
  /-- Residue aggregation and the balanced finite compiler. -/
  | balancedBUnitaryFourier
  /-- Affine / bilinear moving-numerator reciprocal decomposition. -/
  | affineBilinearNumerator
  /-- Four-term contraction identity. -/
  | fourTermContractionIdentity
  /-- `EXACTPRODUCT-CONDITIONED-INVERSECONV-LEVELLS45`. -/
  | exactProductInverseConv
  /-- Exact product collision branch. -/
  | exactProductCollision
  /-- Double Type-II branch. -/
  | doubleTypeII
  /-- The C0 branch. -/
  | c0
  /-- `Ω_H` normalisation source pin. -/
  | omegaH
  /-- Complete Perron / nuclear normalisation source pin. -/
  | completePerronNormalisation
  /-- Fixed-depth product-convolution energy: explicit hypothesis only. -/
  | productConvolutionEnergy
  /-- Retracted: the old post-conditioning index `n = j · (u')⁻¹ mod x`. -/
  | oldPostConditioningIndex
  /-- Retracted: the old wrap `1 + U U' / B`. -/
  | oldWrap
  /-- Erdős problem #287 itself. -/
  | erdos287
  deriving DecidableEq, Fintype, Repr

open ResearchStatus C0FourierNode

/-- The C0 unitary-Fourier ledger. -/
def c0FourierLedger : C0FourierNode → ResearchStatus
  | reciprocalUnitaryFourier => kernelProved
  | balancedBUnitaryFourier => kernelProved
  | affineBilinearNumerator => kernelProved
  | fourTermContractionIdentity => kernelProved
  | exactProductInverseConv => analyticBanked
  | exactProductCollision => analyticBanked
  | doubleTypeII => analyticBanked
  | c0 => conditionalSourcePin
  | omegaH => conditionalSourcePin
  | completePerronNormalisation => conditionalSourcePin
  | productConvolutionEnergy => open_
  | oldPostConditioningIndex => retracted
  | oldWrap => retracted
  | erdos287 => open_

/-- Named status values, exactly as requested by the delta. -/
def reciprocalUnitaryFourierStatus : ResearchStatus := c0FourierLedger reciprocalUnitaryFourier

/-- Status of the balanced-`b` unitary Fourier row. -/
def balancedBUnitaryFourierStatus : ResearchStatus := analyticBanked

/-- Status of the conditioned inverse-convolution row. -/
def exactProductInverseConvStatus : ResearchStatus := c0FourierLedger exactProductInverseConv

/-- Status of the exact-product collision row. -/
def exactProductCollisionStatus : ResearchStatus := c0FourierLedger exactProductCollision

/-- Status of the double Type-II row. -/
def doubleTypeIIStatus : ResearchStatus := c0FourierLedger doubleTypeII

/-- Status of the C0 branch. -/
def c0Status : ResearchStatus := c0FourierLedger c0

/-- Status of the `Ω_H` source pin. -/
def omegaHStatus : ResearchStatus := c0FourierLedger omegaH

/-- Status of the complete Perron / nuclear normalisation source pin. -/
def completePerronNormalisationStatus : ResearchStatus :=
  c0FourierLedger completePerronNormalisation

/-- Status of Erdős #287. -/
def erdos287Status : ResearchStatus := c0FourierLedger erdos287

/-! ## §3  Ledger facts -/

/-- **`finite_fourier_rows_are_kernelProved`.**  `LEAN_PROVED`.  Exactly the four finite
Fourier/algebraic rows of this delta carry `kernelProved`. -/
theorem finite_fourier_rows_are_kernelProved :
    c0FourierLedger reciprocalUnitaryFourier = kernelProved ∧
    c0FourierLedger balancedBUnitaryFourier = kernelProved ∧
    c0FourierLedger affineBilinearNumerator = kernelProved ∧
    c0FourierLedger fourTermContractionIdentity = kernelProved := by
  decide +kernel

/-- **`only_finite_rows_are_kernelProved`.**  `LEAN_PROVED`.  No analytic row, no source pin and
no retracted row is labelled `kernelProved`. -/
theorem only_finite_rows_are_kernelProved :
    ∀ n : C0FourierNode, c0FourierLedger n = kernelProved →
      n = reciprocalUnitaryFourier ∨ n = balancedBUnitaryFourier ∨
      n = affineBilinearNumerator ∨ n = fourTermContractionIdentity := by
  decide +kernel

/-- **`c0_not_kernelProved`.**  `LEAN_PROVED`.  The C0 row is `conditionalSourcePin`: analytically
closed **conditional on formal normalisation**, and in particular not kernel-proved and not
unconditionally banked. -/
theorem c0_not_kernelProved :
    c0Status = conditionalSourcePin ∧ c0Status ≠ kernelProved ∧ c0Status ≠ analyticBanked := by
  decide +kernel

/-- **`source_pins_open`.**  `LEAN_PROVED`.  Both formal source pins are recorded as such and
neither is kernel-proved. -/
theorem source_pins_open :
    omegaHStatus = conditionalSourcePin ∧
    completePerronNormalisationStatus = conditionalSourcePin ∧
    omegaHStatus ≠ kernelProved ∧ completePerronNormalisationStatus ≠ kernelProved := by
  decide +kernel

/-- **`analytic_rows_are_not_kernel_rows`.**  `LEAN_PROVED`.  The analytic research bank rows are
labelled `analyticBanked`, never `kernelProved`. -/
theorem analytic_rows_are_not_kernel_rows :
    exactProductInverseConvStatus = analyticBanked ∧
    exactProductCollisionStatus = analyticBanked ∧
    doubleTypeIIStatus = analyticBanked ∧
    balancedBUnitaryFourierStatus = analyticBanked ∧
    exactProductInverseConvStatus ≠ kernelProved := by
  decide +kernel

/-- **`retracted_architecture_stays_retracted`.**  `LEAN_PROVED`.  The old post-conditioning
index and the old wrap are retracted and must not be re-encoded. -/
theorem retracted_architecture_stays_retracted :
    c0FourierLedger oldPostConditioningIndex = retracted ∧
    c0FourierLedger oldWrap = retracted ∧
    c0FourierLedger oldPostConditioningIndex ≠ kernelProved ∧
    c0FourierLedger oldWrap ≠ kernelProved := by
  decide +kernel

/-- **`erdos287_open`.**  `LEAN_PROVED`.  Erdős #287 is open. -/
theorem erdos287_open : erdos287Status = open_ ∧ erdos287Status ≠ kernelProved := by
  decide +kernel

/-- **`productConvolutionEnergy_is_hypothesis_row`.**  `LEAN_PROVED`.  The fixed-depth
convolution-energy bound is recorded as open; in Lean it exists only as the explicit hypothesis
`ProductConvolutionEnergyHypothesis`, proved non-automatic. -/
theorem productConvolutionEnergy_is_hypothesis_row :
    c0FourierLedger productConvolutionEnergy = open_ ∧
    c0FourierLedger productConvolutionEnergy ≠ kernelProved := by
  decide +kernel

/-- **`fourier_pass_does_not_close_c0`.**  `LEAN_PROVED`.  The kernel-proved finite Fourier row
does not promote the C0 row: the two labels are different, and C0 stays a source pin. -/
theorem fourier_pass_does_not_close_c0 :
    c0FourierLedger reciprocalUnitaryFourier = kernelProved ∧
    c0FourierLedger c0 = conditionalSourcePin ∧
    c0FourierLedger reciprocalUnitaryFourier ≠ c0FourierLedger c0 := by
  decide +kernel

/-! ## §4  The `x` versus `X` firewall -/

/-- **`inv_sqrt_comparison_not_automatic`.**  `LEAN_PROVED`.  There is no free inequality between
`x^{-1/2}` and `X^{-1/2}`: for `x = 1`, `X = 4` the claimed comparison fails.  Hence the exact
finite modulus `x` may not be silently replaced by an analytic parameter `X`; the analytic proof
uses `x ≍ X`, the exact finite theorems of this bank contain `x`. -/
theorem inv_sqrt_comparison_not_automatic :
    ∃ x X : ℝ, 0 < x ∧ 0 < X ∧ ¬ (Real.sqrt x⁻¹ ≤ Real.sqrt X⁻¹) := by
  refine ⟨1, 4, by norm_num, by norm_num, ?_⟩
  intro h
  rw [show ((1 : ℝ))⁻¹ = 1 by norm_num, Real.sqrt_one] at h
  have h4 : Real.sqrt ((4 : ℝ)⁻¹) = 1 / 2 := by
    rw [show ((4 : ℝ))⁻¹ = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4] at h
  norm_num at h

/-! ## §5  The free Möbius splitter dependency order (metadata) -/

/-- The constant-selection layers of the free Möbius splitter discussion.  Metadata only. -/
inductive ConstantLayer
  /-- Structural data of the source. -/
  | structuralData
  /-- Fixed packet costs. -/
  | fixedPacketCosts
  /-- `K_*`. -/
  | kStar
  /-- `K_tr`. -/
  | kTransverse
  /-- `K_Y`, the logarithmic Möbius splitter exponent `Y = L^{K_Y}`. -/
  | kY
  /-- `k`, chosen last. -/
  | kFinal
  deriving DecidableEq, Fintype, Repr

open ConstantLayer

/-- The rank of a constant layer in the selection order. -/
def constantRank : ConstantLayer → ℕ
  | structuralData => 0
  | fixedPacketCosts => 1
  | kStar => 2
  | kTransverse => 3
  | kY => 4
  | kFinal => 5

/-- `DependsOn a b` records that layer `a` is chosen after, hence may depend on, layer `b`. -/
def DependsOn (a b : ConstantLayer) : Prop := constantRank b < constantRank a

/-- **`constant_order_acyclic`.**  `LEAN_PROVED`.  The constant-selection dependency relation is
strictly rank-decreasing, hence acyclic; in particular the chain
`structural data → fixed packet costs → K_* → K_tr → K_Y → k` has no cycle.  This is a statement
about the metadata order, not an analytic theorem. -/
theorem constant_order_acyclic :
    (∀ a : ConstantLayer, ¬ DependsOn a a) ∧
    (∀ a b c : ConstantLayer, DependsOn a b → DependsOn b c → DependsOn a c) ∧
    DependsOn kFinal kY ∧ DependsOn kY kTransverse ∧ DependsOn kTransverse kStar ∧
    DependsOn kStar fixedPacketCosts ∧ DependsOn fixedPacketCosts structuralData := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; simp [DependsOn]
  · intro a b c hab hbc; exact lt_trans hbc hab
  all_goals simp [DependsOn, constantRank]

/-! ## §6  Preservation of the earlier ledger -/

open Erdos287.C0SourceLiftStatus in
/-- **`sourceLift_ledger_still_preserved`.**  `LEAN_PROVED`.  The earlier C0 source-lift rows are
unchanged by this append-only delta. -/
theorem sourceLift_ledger_still_preserved :
    sourceLiftLedger SourceLiftNode.c0Branch = SourceLiftLabel.partialOpen ∧
    sourceLiftLedger SourceLiftNode.erdos287 = SourceLiftLabel.open_ ∧
    sourceLiftLedger SourceLiftNode.sharedGcdOmegaHNormalisationSourcePin45 =
      SourceLiftLabel.openSourcePin := by
  decide +kernel

/-! ## §7  The theorems these rows refer to

* `reciprocalUnitaryFourier` —
  `Erdos287.ReciprocalUnitaryFourier.unitaryFourier_mulConj_sum`,
  `unitaryFourier_column_energy`, `unitaryFourier_bilinear_bound`,
  `unitaryFourier_finset_bilinear_bound`, `zmod_inv_bijOn_units`,
  `reciprocalUnitaryFourier_bilinear_bound`, `transverseTwoCarrierUnitaryFourier`,
  `unitaryFourier_mulConj_sum_composite`.
* `balancedBUnitaryFourier` (finite part) —
  `Erdos287.BalancedBUnitaryFourier.residueAggregate_l2_le_maxFiber`,
  `interval_residue_fibre_card_le`, `intervalResidueAggregate_l2_bound`,
  `reciprocalPhase_fiberwise`, `balancedReciprocalFourier_compiler`.
* `affineBilinearNumerator` —
  `Erdos287.AffineBilinearReciprocalNumerator.zmod_inv_mul_of_isUnit`,
  `affineNumerator_reciprocal_decomposition`,
  `affineBilinearNumerator_reciprocal_decomposition`,
  `affineBilinearNumerator_character_factorisation`, `affineBilinear_rankOne_reduction`.
* `fourTermContractionIdentity` —
  `Erdos287.BalancedBUnitaryFourier.balancedFourier_contraction_identity`.

The two source pins are represented only by the hypothesis shells
`Erdos287.C0PhysicalNormalisation.PerronNuclearNormalisationHypothesis` and
`Erdos287.C0PhysicalNormalisation.OmegaHL2NormalisationHypothesis` (together with the earlier
pointwise shell `Erdos287.ConditionedInverseConv.OmegaHNormalizationHypothesis`), all of which
are proved non-automatic.  The conditional compiler
`Erdos287.C0PhysicalNormalisation.c0_balanced_branch_bound_of` consumes them as explicit
hypotheses and concludes an explicit finite inequality — never “C0 is closed”. -/

end C0UnitaryFourierStatus
end Erdos287
