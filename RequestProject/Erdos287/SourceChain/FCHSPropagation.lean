import RequestProject.Erdos287.SourceChain.W4Route

/-!
# Erdős #287 — propagation of the corrected FCHS term (algebra only)

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**  Everything here is elementary real
algebra about the corrected Pascadi term `pascadiInner F C B0 S H = FC² + B₀CS² + FCHS`.
None of it is a spectral large-sieve estimate.

* `FCHS_le_B0CS2`, `FCHS_le_const_B0CS2` — payment of the extra term: `F ≤ c B₀`, `H ≤ d S`
  give `FCHS ≤ c d B₀ C S²`.
* `pascadiInner_le_two`, `sqrt_pascadiInner_le` — hence `pascadiInner ≤ FC² + 2B₀CS²`
  (and `≤ FC² + (1 + cd)B₀CS²` in general), with the square-root version.
* `pascadi_g_scaling` — the exact `g`-scaling identity for `F = F₀/g`, `C = C₀/g`, in which the
  last term `F₀C₀HS/g` is kept.
* `pascadi_g_scaling_le` — for `g ≥ 1` the scaled expression is at most `1/g` times the
  unscaled `g = 1` expression.
* `pascadi_normalized_identity` — the intermediate normalization in Pascadi's proof
  (with `FCHS/B₀`) equals `HS²√F √(FC² + B₀CS² + FHS)`: the final term is `FHS`, **not** `FCHS`,
  so the two stages are different normalizations.
-/

open Real

namespace Erdos287.SourceChain

/-! ### A. Paying the extra `FCHS` term -/

/-- `F ≤ B₀`, `H ≤ S` (non-negative data) give `FCHS ≤ B₀CS²`. -/
theorem FCHS_le_B0CS2 {F C B0 S H : ℝ} (hF : 0 ≤ F) (hC : 0 ≤ C) (hH : 0 ≤ H) (hS : 0 ≤ S)
    (hFB : F ≤ B0) (hHS : H ≤ S) : F * C * H * S ≤ B0 * C * S ^ 2 := by
  have h1 : F * H ≤ B0 * S := mul_le_mul hFB hHS hH (hF.trans hFB)
  have h2 : 0 ≤ C * S := mul_nonneg hC hS
  nlinarith

/-- Fixed-constant envelope version: `F ≤ c B₀`, `H ≤ d S` give `FCHS ≤ c d B₀CS²`. -/
theorem FCHS_le_const_B0CS2 {F C B0 S H c d : ℝ} (hF : 0 ≤ F) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hS : 0 ≤ S) (hFB : F ≤ c * B0) (hHS : H ≤ d * S) :
    F * C * H * S ≤ c * d * B0 * C * S ^ 2 := by
  have h1 : F * H ≤ (c * B0) * (d * S) := mul_le_mul hFB hHS hH (hF.trans hFB)
  have h2 : 0 ≤ C * S := mul_nonneg hC hS
  have : F * C * H * S = (F * H) * (C * S) := by ring
  rw [this]
  calc (F * H) * (C * S) ≤ ((c * B0) * (d * S)) * (C * S) := mul_le_mul_of_nonneg_right h1 h2
    _ = c * d * B0 * C * S ^ 2 := by ring

/-- `pascadiInner ≤ FC² + 2B₀CS²` when `F ≤ B₀`, `H ≤ S`. -/
theorem pascadiInner_le_two {F C B0 S H : ℝ} (hF : 0 ≤ F) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hS : 0 ≤ S) (hFB : F ≤ B0) (hHS : H ≤ S) :
    pascadiInner F C B0 S H ≤ F * C ^ 2 + 2 * (B0 * C * S ^ 2) := by
  unfold pascadiInner
  linarith [FCHS_le_B0CS2 hF hC hH hS hFB hHS]

/-- Envelope version: `pascadiInner ≤ FC² + (1 + cd) B₀CS²`. -/
theorem pascadiInner_le_const {F C B0 S H c d : ℝ} (hF : 0 ≤ F) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hS : 0 ≤ S) (hFB : F ≤ c * B0) (hHS : H ≤ d * S) :
    pascadiInner F C B0 S H ≤ F * C ^ 2 + (1 + c * d) * (B0 * C * S ^ 2) := by
  unfold pascadiInner
  linarith [FCHS_le_const_B0CS2 hF hC hH hS hFB hHS]

/-- Square-root form of `pascadiInner_le_two`. -/
theorem sqrt_pascadiInner_le {F C B0 S H : ℝ} (hF : 0 ≤ F) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hS : 0 ≤ S) (hFB : F ≤ B0) (hHS : H ≤ S) :
    Real.sqrt (pascadiInner F C B0 S H) ≤ Real.sqrt (F * C ^ 2 + 2 * (B0 * C * S ^ 2)) :=
  Real.sqrt_le_sqrt (pascadiInner_le_two hF hC hH hS hFB hHS)

/-! ### B. The `g`-scaling identity (last term retained) -/

/-- For `g > 0`, `F = F₀/g`, `C = C₀/g`:
`√F · √(FC² + B₀CS² + FCHS) = (√F₀/g) · √(F₀C₀²/g² + B₀C₀S² + F₀C₀HS/g)`. -/
theorem pascadi_g_scaling {F0 C0 B0 S H g : ℝ} (hg : 0 < g) (hF0 : 0 ≤ F0) :
    Real.sqrt (F0 / g) * Real.sqrt (pascadiInner (F0 / g) (C0 / g) B0 S H) =
      Real.sqrt F0 / g *
        Real.sqrt (F0 * C0 ^ 2 / g ^ 2 + B0 * C0 * S ^ 2 + F0 * C0 * H * S / g) := by
  have hgne : g ≠ 0 := hg.ne'
  have hinner : pascadiInner (F0 / g) (C0 / g) B0 S H =
      (F0 * C0 ^ 2 / g ^ 2 + B0 * C0 * S ^ 2 + F0 * C0 * H * S / g) / g := by
    unfold pascadiInner; field_simp
  rw [hinner, ← Real.sqrt_mul (div_nonneg hF0 hg.le)]
  rw [show F0 / g * ((F0 * C0 ^ 2 / g ^ 2 + B0 * C0 * S ^ 2 + F0 * C0 * H * S / g) / g) =
      F0 * (F0 * C0 ^ 2 / g ^ 2 + B0 * C0 * S ^ 2 + F0 * C0 * H * S / g) / g ^ 2 by
    field_simp]
  rw [Real.sqrt_div' _ (by positivity : (0:ℝ) ≤ g ^ 2), Real.sqrt_sq hg.le, Real.sqrt_mul hF0]
  ring

/-- For `g ≥ 1` and non-negative data, the scaled expression is at most `1/g` times the
`g = 1` expression: `√F · √(pascadiInner F C B₀ S H) ≤ (1/g) √F₀ √(F₀C₀² + B₀C₀S² + F₀C₀HS)`. -/
theorem pascadi_g_scaling_le {F0 C0 B0 S H g : ℝ} (hg : 1 ≤ g) (hF0 : 0 ≤ F0) (hC0 : 0 ≤ C0)
    (hS : 0 ≤ S) (hH : 0 ≤ H) :
    Real.sqrt (F0 / g) * Real.sqrt (pascadiInner (F0 / g) (C0 / g) B0 S H) ≤
      Real.sqrt F0 / g * Real.sqrt (pascadiInner F0 C0 B0 S H) := by
  have hg0 : 0 < g := by linarith
  rw [pascadi_g_scaling hg0 hF0]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (Real.sqrt_nonneg _) hg0.le)
  apply Real.sqrt_le_sqrt
  unfold pascadiInner
  have a : F0 * C0 ^ 2 / g ^ 2 ≤ F0 * C0 ^ 2 :=
    div_le_self (by positivity) (one_le_pow₀ hg)
  have b : F0 * C0 * H * S / g ≤ F0 * C0 * H * S := div_le_self (by positivity) hg
  linarith

/-! ### C. Pascadi's intermediate normalization -/

/-- `(B₀/C) √(H²S⁴FC/B₀) √(C²(FC/B₀ + S²) + FCHS/B₀) = HS²√F √(FC² + B₀CS² + FHS)`
for `B₀, C > 0` and non-negative `F, H, S`.  The final term is `FHS`. -/
theorem pascadi_normalized_identity {F C B0 S H : ℝ} (hB0 : 0 < B0) (hC : 0 < C) (hF : 0 ≤ F)
    (hH : 0 ≤ H) (hS : 0 ≤ S) :
    B0 / C * Real.sqrt (H ^ 2 * S ^ 4 * F * C / B0) *
        Real.sqrt (C ^ 2 * (F * C / B0 + S ^ 2) + F * C * H * S / B0) =
      H * S ^ 2 * Real.sqrt F * Real.sqrt (pascadiInnerOld F C B0 S H) := by
  have hB0ne : B0 ≠ 0 := hB0.ne'
  have hCne : C ≠ 0 := hC.ne'
  have e1 : H ^ 2 * S ^ 4 * F * C / B0 = (H * S ^ 2) ^ 2 * (F * (C / B0)) := by
    field_simp
  have e2 : C ^ 2 * (F * C / B0 + S ^ 2) + F * C * H * S / B0 =
      (C / B0) * pascadiInnerOld F C B0 S H := by
    unfold pascadiInnerOld; field_simp
  have hCB : 0 ≤ C / B0 := by positivity
  have hP : 0 ≤ pascadiInnerOld F C B0 S H := by
    unfold pascadiInnerOld; nlinarith [mul_nonneg (mul_nonneg hB0.le hC.le) (sq_nonneg S),
      mul_nonneg (mul_nonneg hF hH) hS, mul_nonneg hF (sq_nonneg C)]
  rw [e1, e2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), Real.sqrt_mul hF,
    Real.sqrt_mul hCB]
  have hs : Real.sqrt (C / B0) * Real.sqrt (C / B0) = C / B0 := Real.mul_self_sqrt hCB
  calc B0 / C * (H * S ^ 2 * (Real.sqrt F * Real.sqrt (C / B0))) *
        (Real.sqrt (C / B0) * Real.sqrt (pascadiInnerOld F C B0 S H))
      = B0 / C * (Real.sqrt (C / B0) * Real.sqrt (C / B0)) *
        (H * S ^ 2 * Real.sqrt F * Real.sqrt (pascadiInnerOld F C B0 S H)) := by ring
    _ = _ := by rw [hs]; field_simp

/-- Regression: the intermediate `FCHS/B₀` stage and the final corrected `FCHS` envelope are
different functions (`F = C = H = S = 1`, `B₀ = 2`). -/
theorem regr_normalizations_differ :
    pascadiInnerOld 1 2 1 1 1 ≠ pascadiInner 1 2 1 1 1 := by
  unfold pascadiInnerOld pascadiInner; norm_num

end Erdos287.SourceChain
