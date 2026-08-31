import Mathlib
import RequestProject.CurrentProgramme.Erdos287BPrimeH0Energy

/-!
# Conditioned inverse-convolution interface and the `Ω_H` firewall — Erdős #287 (append-only)

This module is **append-only** and sits strictly after `Erdos287BPrimeH0Energy`.  It contains
**no** analytic theorem.  It contains:

* §1  a data record and a `Prop` **shell** for the estimate owned by
  `EXACTPRODUCT-CONDITIONED-INVERSECONV-LEVELLS45`, which is **OPEN**;
* §2  the only theorems that mention it, all *conditional*: they take the shell as an explicit
  hypothesis and derive nothing beyond the summed form of what was assumed.  A witness theorem
  records that the shell is **not** vacuous — there are data for which it fails — so it cannot
  be silently discharged;
* §3  the `Ω_H` firewall: `OmegaHNormalizationHypothesis` is likewise a named hypothesis, never
  assumed.  The source pin `SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45` stays **OPEN**.

Nothing in this file asserts, or can be used to assert, that the C0 branch is closed or that
Erdős #287 is proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace ConditionedInverseConv

open Finset

/-! ## §1  The interface shell (OPEN) -/

/-- Schematic data of the conditioned inverse-convolution estimate at moving levels.

`levels` is the finite set of levels `ℓ`; `bilinear ℓ` is the conditioned bilinear form at level
`ℓ`; `energy ℓ` is the corresponding one-row energy; `Ctransfer`, `Lparam`, `K` are the transfer
constant, the size parameter and the logarithmic exponent.  No analytic property of these
fields is assumed anywhere. -/
structure ConditionedInverseConvData where
  /-- The finite set of levels. -/
  levels : Finset ℕ
  /-- The conditioned bilinear form, level by level. -/
  bilinear : ℕ → ℝ
  /-- The one-row energy, level by level. -/
  energy : ℕ → ℝ
  /-- The transfer constant. -/
  Ctransfer : ℝ
  /-- The size parameter entering the logarithmic loss. -/
  Lparam : ℕ
  /-- The exponent of the logarithmic loss. -/
  K : ℕ

/-- **Interface, OPEN.**  The estimate required by
`EXACTPRODUCT-CONDITIONED-INVERSECONV-LEVELLS45`: level by level, the conditioned bilinear form
is bounded by the one-row energy with a logarithmic loss.

This is a *hypothesis shell*.  It is **not** proved anywhere in this repository, and no
declaration assumes it silently: every consumer below takes it as an explicit argument. -/
def ConditionedInverseConvHypothesis (d : ConditionedInverseConvData) : Prop :=
  ∀ ell ∈ d.levels,
    d.bilinear ell ≤ d.Ctransfer * (Real.log ((d.Lparam : ℝ) + 2)) ^ d.K * d.energy ell

/-! ## §2  Conditional consumers -/

/-- **`erdos287_C0_after_conditioned_transfer`.**  `LEAN_PROVED (CONDITIONAL)`.  Given the
conditioned inverse-convolution hypothesis, the level-summed bilinear form obeys the
corresponding summed bound.  This is exactly the assumed estimate, summed; it asserts nothing
further, and in particular does not close C0. -/
theorem erdos287_C0_after_conditioned_transfer
    (d : ConditionedInverseConvData) (hTransfer : ConditionedInverseConvHypothesis d) :
    ∑ ell ∈ d.levels, d.bilinear ell
      ≤ d.Ctransfer * (Real.log ((d.Lparam : ℝ) + 2)) ^ d.K * ∑ ell ∈ d.levels, d.energy ell := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum hTransfer

/-- **`conditionedInverseConv_hypothesis_not_automatic`.**  `LEAN_PROVED`.  The interface shell
is a genuine hypothesis: there are data for which it is false.  Hence no theorem above is
vacuously true, and the shell cannot be discharged by pure logic. -/
theorem conditionedInverseConv_hypothesis_not_automatic :
    ∃ d : ConditionedInverseConvData, ¬ ConditionedInverseConvHypothesis d := by
  refine ⟨⟨{1}, fun _ => 1, fun _ => 0, 0, 0, 0⟩, ?_⟩
  intro h
  have h1 := h 1 (by simp)
  norm_num at h1

/-- **`conditionedInverseConv_hypothesis_satisfiable`.**  `LEAN_PROVED`.  The shell is also not
contradictory: it holds for the empty level set.  Together with the previous theorem this pins
it down as a real, open condition. -/
theorem conditionedInverseConv_hypothesis_satisfiable :
    ∃ d : ConditionedInverseConvData, ConditionedInverseConvHypothesis d := by
  refine ⟨⟨∅, fun _ => 0, fun _ => 0, 0, 0, 0⟩, ?_⟩
  intro ell hell
  simp at hell

/-! ## §3  `Ω_H` firewall (OPEN source pin) -/

/-- Schematic data for the `Ω_H` coefficient and its putative normalisation. -/
structure OmegaHData where
  /-- The index set of the coefficient. -/
  support : Finset ℕ
  /-- The coefficient itself. -/
  OmegaH : ℕ → ℂ
  /-- The claimed normalisation constant. -/
  normalisation : ℝ

/-- **Interface, OPEN source pin.**  The unstated normalisation of `Ω_H`, written as a named
hypothesis: `‖Ω_H(h)‖ ≤ normalisation` on the support.  It is **not** assumed anywhere;
`SHAREDGCD-OMEGAH-NORMALISATION-SOURCEPIN45` remains open. -/
def OmegaHNormalizationHypothesis (d : OmegaHData) : Prop :=
  ∀ h ∈ d.support, ‖d.OmegaH h‖ ≤ d.normalisation

/-- **`omegaH_energy_of_normalization`.**  `LEAN_PROVED (CONDITIONAL)`.  *If* the `Ω_H`
normalisation hypothesis holds, the `ℓ²` mass of `Ω_H` over its support is at most
`#support · normalisation²`.  The normalisation itself is not proved here. -/
theorem omegaH_energy_of_normalization
    (d : OmegaHData) (hNorm : OmegaHNormalizationHypothesis d) :
    ∑ h ∈ d.support, ‖d.OmegaH h‖ ^ 2 ≤ (d.support.card : ℝ) * d.normalisation ^ 2 := by
  have hpt : ∀ h ∈ d.support, ‖d.OmegaH h‖ ^ 2 ≤ d.normalisation ^ 2 := by
    intro h hh
    exact pow_le_pow_left₀ (norm_nonneg _) (hNorm h hh) 2
  calc ∑ h ∈ d.support, ‖d.OmegaH h‖ ^ 2 ≤ ∑ _h ∈ d.support, d.normalisation ^ 2 :=
        Finset.sum_le_sum hpt
    _ = (d.support.card : ℝ) * d.normalisation ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **`omegaH_normalization_not_automatic`.**  `LEAN_PROVED`.  The `Ω_H` normalisation is a
genuine hypothesis: there are data for which it fails.  No declaration of this repository may
therefore quietly encode it. -/
theorem omegaH_normalization_not_automatic :
    ∃ d : OmegaHData, ¬ OmegaHNormalizationHypothesis d := by
  refine ⟨⟨{0}, fun _ => 1, 0⟩, ?_⟩
  intro h
  have h0 := h 0 (by simp)
  norm_num at h0

end ConditionedInverseConv
end Erdos287
