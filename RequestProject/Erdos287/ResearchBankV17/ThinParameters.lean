import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Erdős #287 — Research Bank V17 §1: the fixed Route-C-thin instance

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Recorded exactly (FINITE REGRESSION / parameter record):

    δ = 1/40000,  L = 41252000,  K = 2^L,  P = 12 K,  a = 28593810.

`K` is never evaluated (it has about 12.4 million decimal digits); every statement about it is
symbolic.

Kernel-proved (LEAN BANK):
* `L_mul_delta` — `L δ = 10313/10`;
* `L_ge_threshold` — `L δ log 2 ≥ 704` (Mathlib's certified `log 2 > 0.6931471803`), i.e. the
  fixed `L` is at least the uniform-thinning length `704/(δ log 2)`.
-/

namespace Erdos287
namespace ResearchBankV17
namespace ThinParameters

/-- `δ = 1/40000`. -/
def delta : ℚ := 1 / 40000

/-- `L = 41252000`.  Declared with `irreducible_def` so that neither the elaborator nor the kernel
ever tries to evaluate `2^L` (the value is available through the equation `L_def`). -/
irreducible_def L : ℕ := 41252000

/-- `K = 2^L` (symbolic). -/
def K : ℕ := 2 ^ L

/-- `P = 12 K`. -/
def P : ℕ := 12 * K

/-- `a = 28593810`. -/
def aParam : ℕ := 28593810

theorem K_pos : 0 < K := pow_pos (by norm_num) _

theorem L_mul_delta : (L : ℚ) * delta = 10313 / 10 := by rw [L_def]; unfold delta; norm_num

/-- **`L δ log 2 ≥ 704`.** -/
theorem L_ge_threshold : (704 : ℝ) ≤ (L : ℝ) * ((delta : ℚ) : ℝ) * Real.log 2 := by
  have h := Real.log_two_gt_d9
  rw [L_def]; unfold delta; push_cast
  nlinarith

end ThinParameters
end ResearchBankV17
end Erdos287
