import Mathlib
import RequestProject.CurrentProgramme.LowConductorSiegelWalfisz
import RequestProject.CurrentProgramme.SmallQ34LSRoute

/-!
# CurrentProgramme (post-Balanced7 pass) §7 — the SmallQ `3+4` conditional compiler

`AFFINE287-SP2-SMALLQ-34LS-NORMALIZATION45` remains the **first exact residual**: what is
missing is the coefficient/source normalisation, not exponent capacity.  This module banks
the purely logical *compiler* that assembles the three children of the replacement provider

* the conductor-split `3+4` multiplicative large sieve (§5),
* the tiny-modulus Siegel–Walfisz child (§6),
* the imprimitive-conductor/normalisation defect,

into the SmallQ target bound `|S| ≤ ε X / log X`, by a triangle inequality with an explicit
`ε/3` budget for each child.

Nothing analytic is proved.  The bundle `BalancedSevenSmallQ34LSInputs` (plural — distinct
from the pass-1 literal obligation socket `BalancedSevenSmallQ34LSInput`) is **not**
inhabited; `smallQ34LSInputs_not_automatic` records that.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos287
namespace PostBalanced7Pro

/-! ## §7.1  The target -/

/-- The SmallQ target: the packet is `o(X / log X)` at the declared budget `ε`. -/
def SmallQTargetBound (S X eps : ℝ) : Prop := |S| ≤ eps * X / Real.log X

/-! ## §7.2  The three-child bundle -/

/-- **`BalancedSevenSmallQ34LSInputs`** — `CONDITIONAL BUNDLE / NOT INHABITED`.

The three children of the replacement SmallQ provider, each with an `ε/3` budget, together
with the exact reassembly of the physical SmallQ packet.  The individual analytic bounds are
*hypotheses*: they are supplied by the (uninhabited) sockets of §5 and §6 and by the
outstanding normalisation residual. -/
structure BalancedSevenSmallQ34LSInputs
    (sTotal pLargeSieve pSiegelWalfisz pNormalisation X eps : ℝ) : Prop where
  /-- The scale is nontrivial and the declared saving is genuine. -/
  scale : 3 ≤ X ∧ 0 < eps
  /-- Exact reassembly of the physical SmallQ packet from its three children. -/
  decomposition : sTotal = pLargeSieve + pSiegelWalfisz + pNormalisation
  /-- The `3+4` multiplicative large-sieve child is inside its `ε/3` budget. -/
  largeSieve_budget : |pLargeSieve| ≤ eps * X / Real.log X / 3
  /-- The tiny-modulus Siegel–Walfisz child is inside its `ε/3` budget. -/
  siegelWalfisz_budget : |pSiegelWalfisz| ≤ eps * X / Real.log X / 3
  /-- The imprimitive-conductor normalisation child is inside its `ε/3` budget.
  This is the field that `AFFINE287-SP2-SMALLQ-34LS-NORMALIZATION45` has to supply. -/
  normalisation_budget : |pNormalisation| ≤ eps * X / Real.log X / 3

/-- **`smallQ34LS_compiler`.**  `LEAN_PROVED` (purely logical / conditional).

Given the three-child bundle, the SmallQ packet meets its target.  This is a triangle
inequality, **not** an analytic theorem: it does not assert that any child bound holds. -/
theorem smallQ34LS_compiler
    {sTotal pLargeSieve pSiegelWalfisz pNormalisation X eps : ℝ}
    (h : BalancedSevenSmallQ34LSInputs sTotal pLargeSieve pSiegelWalfisz pNormalisation X eps) :
    SmallQTargetBound sTotal X eps := by
  have h1 : |sTotal| ≤ |pLargeSieve| + |pSiegelWalfisz| + |pNormalisation| := by
    rw [h.decomposition]
    have ha := abs_add_le (pLargeSieve + pSiegelWalfisz) pNormalisation
    have hb := abs_add_le pLargeSieve pSiegelWalfisz
    linarith
  have h2 := h.largeSieve_budget
  have h3 := h.siegelWalfisz_budget
  have h4 := h.normalisation_budget
  unfold SmallQTargetBound
  linarith

/-- **`smallQ34LS_compiler_pointwise`.**  `LEAN_PROVED`.

The same conclusion in the raw two-sided form. -/
theorem smallQ34LS_compiler_pointwise
    {sTotal pLargeSieve pSiegelWalfisz pNormalisation X eps : ℝ}
    (h : BalancedSevenSmallQ34LSInputs sTotal pLargeSieve pSiegelWalfisz pNormalisation X eps) :
    -(eps * X / Real.log X) ≤ sTotal ∧ sTotal ≤ eps * X / Real.log X :=
  abs_le.mp (smallQ34LS_compiler h)

/-- **`smallQ34LSInputs_not_automatic`.**  `LEAN_PROVED`.

The bundle is a genuine restriction: the compiler does not manufacture its own hypotheses. -/
theorem smallQ34LSInputs_not_automatic :
    ∃ (sTotal pLargeSieve pSiegelWalfisz pNormalisation X eps : ℝ),
      ¬ BalancedSevenSmallQ34LSInputs sTotal pLargeSieve pSiegelWalfisz pNormalisation X eps := by
  refine ⟨0, 0, 0, 0, 0, 0, ?_⟩
  intro h
  have h2 : (3 : ℝ) ≤ 0 := h.scale.1
  linarith

/-- **`smallQ34LS_residual_is_normalisation`.**  `LEAN_PROVED`.

The bundle is *not* obtainable from the large-sieve and Siegel–Walfisz children alone: with
both of those children at zero, the conclusion still fails unless the normalisation child is
controlled.  This is the exact sense in which the outstanding SmallQ obligation is
coefficient/source normalisation rather than exponent capacity. -/
theorem smallQ34LS_residual_is_normalisation :
    ∃ (sTotal pNormalisation X eps : ℝ),
      |(0 : ℝ)| ≤ eps * X / Real.log X / 3 ∧
      sTotal = 0 + 0 + pNormalisation ∧
      ¬ SmallQTargetBound sTotal X eps := by
  have hlog : 1 < Real.log 3 := by
    have h1 : Real.log (Real.exp 1) < Real.log 3 :=
      Real.log_lt_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
    simpa using h1
  refine ⟨1, 1, 3, 1 / 100, ?_, by norm_num, ?_⟩
  · have h0 : (0 : ℝ) ≤ (1 / 100 : ℝ) * 3 / Real.log 3 / 3 :=
      div_nonneg (div_nonneg (by norm_num) (by linarith)) (by norm_num)
    simpa using h0
  · unfold SmallQTargetBound
    rw [abs_one]
    intro hcon
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < Real.log 3)] at hcon
    nlinarith

end PostBalanced7Pro
end Erdos287
