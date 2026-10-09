import RequestProject.Erdos287.ResearchBankV16.RouteCParameters

/-!
# Erdős #287 — Research Bank V16 §5: the relaxed Route-C pair budget

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The corrected positive-energy interface for Route C.  The Route-B numerical estimate
`A_* W_F < 187` is **not** used anywhere in V16.

With normalization `N > 0` and a uniform error `η ≥ 0`, suppose

    S0 ≤ (1 + η) N,     (μ_F − η) N ≤ S1,     Pair ≤ (A_C W_F + 90 + err + η) N,

where `err` is the frozen approximation error.  If

    η · (1 + 1/99 + 350) < μ_F − (A_C W_F + 90 + err)/99 − 350,

then the consumer score is positive: `S1 − Pair/99 − 350 S0 > 0`.

Kernel-proved (LEAN BANK):
* `relaxed_score_positive` — the rational/real implication above;
* `eta_choice` — for any margin `m > 0`, the choice `η = m/400` satisfies the hypothesis;
* `eventual_score_positive` — the same with `o(1)` written as explicit eventual/ε quantifiers:
  if the three normalized estimates hold eventually for every `η > 0`, then eventually the
  consumer score is positive.  This theorem is **conditional**: the baseline estimate is a
  hypothesis (supplied by `RouteCBaselineProvider` in `ConditionalRouteCImplication`).
-/

namespace Erdos287
namespace ResearchBankV16
namespace RelaxedPairBudget

open RouteCParameters

/-- **Relaxed pair budget: the consumer score stays positive.** -/
theorem relaxed_score_positive {N S0 S1 Pair muF WF err η A : ℝ} (hN : 0 < N)
    (h0 : S0 ≤ (1 + η) * N) (h1 : (muF - η) * N ≤ S1)
    (hP : Pair ≤ (A * WF + 90 + err + η) * N)
    (hm : η * (1 + 1 / 99 + 350) < muF - (A * WF + 90 + err) / 99 - 350) :
    0 < S1 - Pair / 99 - 350 * S0 := by
  have hm' := mul_lt_mul_of_pos_right hm hN
  nlinarith

/-- The choice `η = m/400` fits any positive margin `m`. -/
theorem eta_choice {m : ℝ} (hm : 0 < m) : (m / 400) * (1 + 1 / 99 + 350) < m := by
  nlinarith

/-- **Eventual form** (`o(1)` as explicit quantifiers).  Conditional on the three eventual
normalized estimates, in particular on the baseline estimate for `Pair`. -/
theorem eventual_score_positive (S0 S1 Pair N : ℕ → ℝ) {muF WF err A : ℝ}
    (hm : 0 < muF - (A * WF + 90 + err) / 99 - 350)
    (h0 : ∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, 0 < N M ∧ S0 M ≤ (1 + η) * N M)
    (h1 : ∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, (muF - η) * N M ≤ S1 M)
    (hP : ∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, Pair M ≤ (A * WF + 90 + err + η) * N M) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, 0 < S1 M - Pair M / 99 - 350 * S0 M := by
  set m := muF - (A * WF + 90 + err) / 99 - 350
  have hη : (0 : ℝ) < m / 400 := by positivity
  obtain ⟨Ma, ha⟩ := h0 _ hη
  obtain ⟨Mb, hb⟩ := h1 _ hη
  obtain ⟨Mc, hc⟩ := hP _ hη
  refine ⟨max Ma (max Mb Mc), fun M hM => ?_⟩
  obtain ⟨hN, e0⟩ := ha M (le_trans (le_max_left _ _) hM)
  have e1 := hb M (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM)
  have e2 := hc M (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM)
  exact relaxed_score_positive hN e0 e1 e2 (eta_choice hm)

/-- The Route-C baseline form `A_C W_F + 90` with `A_C = 1000273/273000`. -/
theorem baseline_form (WF : ℝ) :
    ((A_C : ℚ) : ℝ) * WF + 90 = (1000273 / 273000 : ℝ) * WF + 90 := by
  unfold A_C; push_cast; ring

end RelaxedPairBudget
end ResearchBankV16
end Erdos287
