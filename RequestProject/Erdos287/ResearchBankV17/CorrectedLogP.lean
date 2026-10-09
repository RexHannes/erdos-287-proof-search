import RequestProject.Erdos287.ResearchBankV17.ThinParameters

/-!
# Erdős #287 — Research Bank V17 §1: the corrected `log P`

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

**Regression repaired.**  An earlier verifier used `L log 2 + log 3` for `log P`.  That quantity is
`log(3K)`, not `log(12K) = log P`.

Kernel-proved (LEAN BANK):
* `log_twelve_pow` — for every `L`: `log(12 · 2^L) = (L + 2) log 2 + log 3`;
* `logP_eq` — `log P = (L + 2) log 2 + log 3` for the fixed thin `P = 12 · 2^41252000`;
* `old_formula_is_log_3K` — `L log 2 + log 3 = log(3K)` (REPAIRED / RETIRED formula);
* `old_formula_ne_logP` — `L log 2 + log 3 ≠ log P`; the gap is exactly `2 log 2`
  (`logP_sub_old`);
* `a_sub_logP_bounds` — `99 < a − log P < 101` for `a = 28593810`, from Mathlib's certified
  bounds on `log 2` and `e`.
-/

namespace Erdos287
namespace ResearchBankV17
namespace CorrectedLogP

open ThinParameters

/-- **`log(12 · 2^L) = (L + 2) log 2 + log 3`** (every `L`). -/
theorem log_twelve_pow (n : ℕ) :
    Real.log ((12 * 2 ^ n : ℕ) : ℝ) = ((n : ℝ) + 2) * Real.log 2 + Real.log 3 := by
  push_cast
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
    show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow]
  push_cast; ring

/-- **The corrected identity `log P = (L + 2) log 2 + log 3`.** -/
theorem logP_eq : Real.log (P : ℝ) = ((L : ℝ) + 2) * Real.log 2 + Real.log 3 := by
  exact log_twelve_pow L

/-- The old formula computes `log(3K)`. -/
theorem old_formula_is_log_3K :
    (L : ℝ) * Real.log 2 + Real.log 3 = Real.log ((3 * K : ℕ) : ℝ) := by
  unfold K; push_cast
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; ring

/-- The gap between the corrected and the old formula is `2 log 2`. -/
theorem logP_sub_old :
    Real.log (P : ℝ) - ((L : ℝ) * Real.log 2 + Real.log 3) = 2 * Real.log 2 := by
  rw [logP_eq]; ring

/-- **Negative fixture: the old formula is NOT `log P`.** -/
theorem old_formula_ne_logP : (L : ℝ) * Real.log 2 + Real.log 3 ≠ Real.log (P : ℝ) := by
  intro h
  have := logP_sub_old
  rw [← h, sub_self] at this
  have h2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  linarith

/-- `log 3 > 1` (from `e < 3`). -/
theorem one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9; linarith

/-- `log 3 < 2 log 2` (from `3 < 4`). -/
theorem log_three_lt : Real.log 3 < 2 * Real.log 2 := by
  rw [← Real.log_rpow (by norm_num)]
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- **`99 < a − log P < 101`.** -/
theorem a_sub_logP_bounds :
    99 < (aParam : ℝ) - Real.log (P : ℝ) ∧ (aParam : ℝ) - Real.log (P : ℝ) < 101 := by
  rw [logP_eq]
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have h3 := one_lt_log_three
  have h4 := log_three_lt
  rw [L_def]; unfold aParam
  push_cast
  constructor <;> nlinarith

end CorrectedLogP
end ResearchBankV17
end Erdos287
