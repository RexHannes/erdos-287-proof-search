import RequestProject.Erdos287.ResearchBankV17.ThinConsumer
import RequestProject.Erdos287.ResearchBankV17.UniformThinning
import RequestProject.Erdos287.ResearchBankV17.ThinSupportLedger
import RequestProject.Erdos287.ResearchBankV16.ScopeFirewalls

/-!
# Erdős #287 — Research Bank V17: thin effectivity firewall

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `eventual_gives_no_bound` — an eventual statement `∃ M₀, ∀ M ≥ M₀, Q M` yields no explicit
  threshold: for every candidate `B` there is an eventually-true `Q` failing at `B`;
* `no_uniform_x0` (re-export) — no uniformity in `x` and `δ` simultaneously;
* `logP_regression` (re-export) — the old verifier formula is `log(3K) ≠ log P`;
* `v17_effectivity_firewall` — the V14 effectivity firewall is unchanged.
-/

namespace Erdos287
namespace ResearchBankV17
namespace ThinEffectivityFirewall

open ResearchBankV14

/-- **An eventual statement yields no explicit threshold.** -/
theorem eventual_gives_no_bound (B : ℕ) :
    ∃ Q : ℕ → Prop, (∃ M₀ : ℕ, ∀ M ≥ M₀, Q M) ∧ ¬ ∀ M ≥ B, Q M :=
  ⟨fun M => B < M, ⟨B + 1, fun M hM => by omega⟩, fun h => lt_irrefl B (h B le_rfl)⟩

theorem no_uniform_x0 :
    ¬ ∃ x₀ : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 40000 → ∀ x ≥ x₀, 0 < 1 - 1 / (δ * x) :=
  UniformThinning.no_uniform_x0.2

theorem logP_regression :
    (ThinParameters.L : ℝ) * Real.log 2 + Real.log 3 =
        Real.log ((3 * ThinParameters.K : ℕ) : ℝ) ∧
      (ThinParameters.L : ℝ) * Real.log 2 + Real.log 3 ≠ Real.log (ThinParameters.P : ℝ) :=
  ⟨CorrectedLogP.old_formula_is_log_3K, CorrectedLogP.old_formula_ne_logP⟩

/-- **The V14 effectivity firewall is unchanged in V17.** -/
theorem v17_effectivity_firewall (A : ℝ) :
    EffectivityFirewall.compilerUsefulHeightBound = none ∧
      EffectivityFirewall.explicitAnalyticThreshold = none ∧
      ResearchBankV11.AnalyticActivation.current_M_an A = none ∧
      EffectivityFirewall.finiteSpliceClosed = false ∧
      ResearchBankV13.AuditedEndpoint.concreteFinitePayload =
        ResearchBankV13.AuditedEndpoint.PayloadStatus.notSupplied :=
  EffectivityFirewall.effectivity_firewall A

end ThinEffectivityFirewall
end ResearchBankV17
end Erdos287
