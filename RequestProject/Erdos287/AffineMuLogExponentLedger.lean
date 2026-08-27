import Mathlib
import RequestProject.Erdos287.FixedCertificateSingletonParameters

/-!
# V15, Part 5 — the short-line **exponent** ledger (rational arithmetic only)

This file contains *only* rational exponent arithmetic.  It reuses the parameters already
banked by the project:

* `ν₀ = 16623/100000` (`Erdos287.FordData.nu0`, cast as `Erdos287.Singleton.nu0R`),
* `σ = ν₀ − 2ε` (`Erdos287.Singleton.sigmaOf`) under the same explicit rational hypothesis
  `AdmissibleEps ε : 0 < ε < ν₀/100`.

We define `δ₀ = 1/6 − σ` and prove

* `mulog_delta0_pos`               : `δ₀ > 0`,
* `mulog_shortLine_exponent_eq`    : `σ + 2/3 + 1/6 = 1 − δ₀`,
* `mulog_shortLine_exponent_lt_one`: `σ + 2/3 + 1/6 < 1`.

## Honesty statement

**No analytic estimate is proved or assumed here.**  In particular nothing of the form
"short-line contribution `= O(X^{1−δ₀})`" is a theorem of this project: the analytic
summation object does not exist in the repository, and an exponent inequality is not an
estimate.

Status:

`AFFINE287-SHORTLINE-MR-ROUTER45 : EXPONENT_CORE_PROVED / ANALYTIC_SUMMATION_EXTERNAL`
`AFFINE287-LINE-DICHOTOMY45 : EXPONENT CORE PROVED; ANALYTIC SHORT-LINE ROUTER EXTERNAL`
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace MuLog

open Erdos287.Singleton

/-- The exponent saving `δ₀ = 1/6 − σ`. -/
noncomputable def delta0Of (eps : ℝ) : ℝ := 1 / 6 - sigmaOf eps

/-- **`mulog_delta0_pos`** — `δ₀ > 0`, from the banked `σ < 1/6`. -/
theorem mulog_delta0_pos {eps : ℝ} (h : AdmissibleEps eps) : 0 < delta0Of eps := by
  have := sigma_lt_one_sixth h
  simp only [delta0Of]
  linarith

/-- **`mulog_shortLine_exponent_eq`** — the exponent identity `σ + 2/3 + 1/6 = 1 − δ₀`. -/
theorem mulog_shortLine_exponent_eq (eps : ℝ) :
    sigmaOf eps + 2 / 3 + 1 / 6 = 1 - delta0Of eps := by
  simp only [delta0Of]; ring

/-- **`mulog_shortLine_exponent_lt_one`** — hence `σ + 2/3 + 1/6 < 1`.

This is an inequality between rational exponents and **nothing more**; it is not an
analytic bound on any sum. -/
theorem mulog_shortLine_exponent_lt_one {eps : ℝ} (h : AdmissibleEps eps) :
    sigmaOf eps + 2 / 3 + 1 / 6 < 1 := by
  have hd := mulog_delta0_pos h
  rw [mulog_shortLine_exponent_eq]
  linarith

/-- The purely rational form of the ledger, with `σ` a free rational parameter below `1/6`
(no reference to `ε` at all). -/
theorem mulog_shortLine_exponent_lt_one_rat {sigma : ℚ} (h : sigma < 1 / 6) :
    sigma + 2 / 3 + 1 / 6 < 1 := by linarith

/-- The exact numerical value of the saving at `ε → 0`: `δ₀ = 1/6 − ν₀ = 131/300000 > 0`. -/
theorem mulog_delta0_unshrunk_value : (1 : ℚ) / 6 - FordData.nu0 = 131 / 300000 := by
  norm_num [FordData.nu0]

end MuLog
end Erdos287
