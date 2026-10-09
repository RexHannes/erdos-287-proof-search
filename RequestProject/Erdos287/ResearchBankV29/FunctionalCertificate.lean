import RequestProject.Erdos287.ResearchBankV29.SourceNormalization
import RequestProject.Erdos287.ResearchBankV28.ExactParameterInstantiation

/-!
# Erdős #287 — Research Bank V29 §10–§11: functional certificate and score formula

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## §10 Functional certificate — FINITE CERTIFIED INPUT

A repository-wide search (all `.lean` files and all reports) for `7147687` and `98278402` finds
only the V28 constants `muLo`, `WHi`, their V28 report and `ARISTOTLE_SUMMARY.md`.  **No rational
certificate data (quadrature nodes, interval enclosures, optimisation witnesses) exists in the
repository**, so `μ_F > 7147687/10000` and `W_F < 98278402/10000` cannot be derived here.  They are
isolated in the narrowly named `FunctionalKernelCertificate` (NOT inside any analytic provider
bundle), labelled FINITE CERTIFIED INPUT, with provenance string `certificateProvenance`.

The exponent `−1079/1900` (V27 `realCorrectionExponent`) likewise has no derivation formula in the
repository; only `−1079/1900 = −1/2 − 129/1900` and its sign comparisons are checked
(`exponent_supplied_facts`).  Missing derivation: the real-correction analytic estimate producing
the `129/1900` excess.  The witness `8746001/25000000` (V28) is in the same situation.

## §11 Score formula — MISMATCH REPORTED

The consumer of the final theorem is `ResearchBankV16.RouteCParameters.RouteCMarginCheck`
(through `ThinMarginCheck`), i.e. `350 + (A_C W_hi + 90 + err)/99 < μ_lo`.  With `err = −423/5`
(`errFinal`) the quantity actually consumed is

    μ_lo − (A_C W_hi + 27/5)/99 − 350          (= 12093752057/12285000000),

**without** the `− 1/20` of the task's formula.  The task formula equals the consumed quantity
minus `1/20` (`score_formula_relation`) and equals `11479502057/12285000000 > 0`; since it is
strictly smaller, its positivity IMPLIES the consumer check (`task_score_implies_consumer`), but
it is NOT literally the consumed quantity: the `1/20` is an unconsumed reserve slack.
-/

namespace Erdos287
namespace ResearchBankV29
namespace FunctionalCertificate

open ResearchBankV16.RouteCParameters ResearchBankV17.ThinFunctional
open ResearchBankV28.ExactParameterInstantiation

/-- Provenance of the certified functional inequalities. -/
def certificateProvenance : String :=
  "Route-C functional certificate (FINITE CERTIFIED INPUT): mu_F > 7147687/10000 and " ++
  "W_F < 98278402/10000, supplied as audited numerical bounds in the V28/V29 task statements; " ++
  "no rational certificate data exists in this repository."

/-- **FINITE CERTIFIED INPUT** — only the two certified inequalities (plus `W_F ≥ 0`). -/
structure FunctionalKernelCertificate (muF WF : ℝ) : Prop where
  muF_gt : ((7147687 / 10000 : ℚ) : ℝ) < muF
  WF_lt : WF < ((98278402 / 10000 : ℚ) : ℝ)
  WF_nonneg : 0 ≤ WF

theorem mu_F_lower {muF WF : ℝ} (C : FunctionalKernelCertificate muF WF) :
    ((7147687 / 10000 : ℚ) : ℝ) < muF := C.muF_gt

theorem W_F_upper {muF WF : ℝ} (C : FunctionalKernelCertificate muF WF) :
    WF < ((98278402 / 10000 : ℚ) : ℝ) := C.WF_lt

/-- The certificate is exactly the frozen thin certificate at `(muLo, WHi)` (LEAN BANK). -/
theorem certificate_iff_thin (muF WF : ℝ) :
    FunctionalKernelCertificate muF WF ↔ ThinFunctionalCertificate muLo WHi muF WF := by
  constructor
  · intro C; exact ⟨by simpa [muLo] using C.muF_gt, by simpa [WHi] using C.WF_lt, C.WF_nonneg⟩
  · intro C
    exact ⟨by simpa [muLo] using C.muF_gt, by simpa [WHi] using C.WF_lt, C.WF_nonneg⟩

/-- The exponent `−1079/1900`: supplied value, rational facts only (LEAN BANK). -/
theorem exponent_supplied_facts :
    ResearchBankV27.SmoothFrequencyRecovery.realCorrectionExponent = -1 / 2 - 129 / 1900 ∧
      ResearchBankV27.SmoothFrequencyRecovery.realCorrectionExponent < -(1 / 1100) :=
  ⟨ResearchBankV27.SmoothFrequencyRecovery.real_correction_exponent_facts.2.2.2,
    ResearchBankV27.SmoothFrequencyRecovery.real_correction_exponent_facts.2.2.1⟩

/-- The quantity literally consumed by the final consumer. -/
def consumedMargin : ℚ := muLo - (A_C * WHi + baselineConst + errFinal) / pairDen - threshold

/-- The task's score formula. -/
def taskScore : ℚ := muLo - (A_C * WHi + 27 / 5) / 99 - 350 - 1 / 20

/-- **The consumer check is positivity of `consumedMargin`** (LEAN BANK, from definitions). -/
theorem consumer_check_iff : ThinMarginCheck muLo WHi errFinal ↔ 0 < consumedMargin := by
  unfold ThinMarginCheck RouteCMarginCheck consumedMargin
  constructor <;> intro h <;> linarith

/-- The consumed margin in closed form (LEAN BANK). -/
theorem consumedMargin_value :
    consumedMargin = muLo - (A_C * WHi + 27 / 5) / 99 - 350 ∧
      consumedMargin = 12093752057 / 12285000000 := by
  unfold consumedMargin muLo WHi A_C baselineConst errFinal pairDen threshold
  constructor <;> norm_num

/-- **Score-formula relation / mismatch** (LEAN BANK): task score = consumed margin − 1/20. -/
theorem score_formula_relation : taskScore = consumedMargin - 1 / 20 := by
  unfold taskScore consumedMargin baselineConst errFinal pairDen threshold; ring

/-- The task score value (LEAN BANK). -/
theorem taskScore_value : taskScore = 11479502057 / 12285000000 ∧ (0 : ℚ) < taskScore := by
  unfold taskScore muLo WHi A_C; constructor <;> norm_num

/-- **Task score positivity implies the consumer check** (LEAN BANK). -/
theorem task_score_implies_consumer (h : 0 < taskScore) : ThinMarginCheck muLo WHi errFinal := by
  rw [consumer_check_iff]; rw [score_formula_relation] at h; linarith

/-- **The task score is NOT the consumed quantity** (LEAN BANK): they differ by exactly `1/20`. -/
theorem taskScore_ne_consumed : taskScore ≠ consumedMargin := by
  rw [score_formula_relation]; norm_num

end FunctionalCertificate
end ResearchBankV29
end Erdos287
