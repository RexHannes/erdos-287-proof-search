import RequestProject.Erdos287.ResearchBankV16.ConditionalRouteCImplication
import RequestProject.Erdos287.ResearchBankV17.ThinFunctionalCertificate

/-!
# Erdős #287 — Research Bank V17: the Route-C-thin consumer

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The thin consumer uses the V16 Route-C deterministic consumer (26 groups, score threshold `350`,
`c_C = 46/125`), with the corrected thin functional certificate (after the corrected
`log P = (L+2) log 2 + log 3`).

* `thin_eventually_no_counterexample` (LEAN CONDITIONAL) — thin functional certificate + exact
  thin margin check + S0/S1 contracts + the (never constructed) Route-C baseline provider
  ⟹ no counterexample with maximum `M`, for all sufficiently large `M`.
* `thin_margin_is_certified_input_dependent` — the margin is positive only through the certified
  inputs; a certificate with the wrong bounds fails the check (`bad_bounds_fail_check`).
-/

namespace Erdos287
namespace ResearchBankV17
namespace ThinConsumer

open ResearchBankV16 ResearchBankV16.RouteCParameters ResearchBankV16.RouteCConsumer
open ResearchBankV16.ConditionalRouteCImplication ThinFunctional
open ResearchBankV13.FiniteRepresentationModel
open ResearchBankV14.ConditionalAsymptoticImplication (S0Contract S1Contract)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The thin consumer (conditional).** -/
theorem thin_eventually_no_counterexample {muLo WHi err : ℚ} (τ : FixedTupleC V)
    (W : WeightSystem τ) (N : ℕ → ℝ) {muF WF : ℝ}
    (C : ThinFunctionalCertificate muLo WHi muF WF) (hchk : ThinMarginCheck muLo WHi err)
    (h0 : S0Contract (S0 τ W) N) (h1 : S1Contract (S1 τ W) N muF)
    (hP : RouteCBaselineProvider τ W N WF ((err : ℚ) : ℝ)) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, NoCounterexampleAt M :=
  routeC_eventually_no_counterexample τ W N (toRouteC C) hchk h0 h1 hP

/-- The exact check is a genuine constraint: bounds `μ_lo = 350`, `W_hi = 0`, `err = 0` fail it. -/
theorem bad_bounds_fail_check : ¬ ThinMarginCheck 350 0 0 := by
  unfold ThinMarginCheck RouteCMarginCheck threshold pairDen baselineConst; norm_num

/-- The margin is certified-input dependent. -/
theorem thin_margin_is_certified_input_dependent :
    (∀ {muLo WHi err : ℚ} {muF WF : ℝ}, ThinFunctionalCertificate muLo WHi muF WF →
      ThinMarginCheck muLo WHi err →
        0 < muF - (((A_C : ℚ) : ℝ) * WF + 90 + ((err : ℚ) : ℝ)) / 99 - 350) ∧
    ¬ ThinMarginCheck 350 0 0 :=
  ⟨fun C h => thin_margin_pos C h, bad_bounds_fail_check⟩

end ThinConsumer
end ResearchBankV17
end Erdos287
