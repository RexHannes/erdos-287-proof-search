import RequestProject.Erdos287.ResearchBankV16.ConditionalRouteCImplication
import RequestProject.Erdos287.ResearchBankV16.BalancedBlowup26
import RequestProject.Erdos287.ResearchBankV14.EffectivityFirewall

/-!
# Erdős #287 — Research Bank V16: scope firewalls

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `routeB_constants_not_imported` (FINITE REGRESSION) — the Route-B constants `c = 37/100` and
  translation buffer `1001/1000` both FAIL the Route-C localization inequality;
* `certificate_does_not_give_S0` — a Route-C functional certificate can hold while the actual
  zeroth-moment contract fails (the functional certificate carries no arithmetic moment);
* `baseline_provider_not_vacuous` — `RouteCBaselineProvider` is falsifiable;
* `v16_effectivity_firewall` — the V14 effectivity firewall is unchanged: no explicit analytic
  threshold, no compiler height bound, finite splice not closed.
-/

namespace Erdos287
namespace ResearchBankV16
namespace ScopeFirewalls

open RouteCParameters ContactLocalizationC ConditionalRouteCImplication
open ResearchBankV14.ConditionalAsymptoticImplication (S0Contract)
open ResearchBankV14

/-- **Route-B constants are not imported into Route C.** -/
theorem routeB_constants_not_imported :
    1 < (37 / 100 : ℚ) * RC ∧ 1 < cC * (diffRatio * (1001 / 1000) ^ 2) ∧ cC * RC < 1 :=
  ⟨routeB_c_fails_with_RC, routeB_buffer_fails, cC_mul_RC_lt_one⟩

/-- A certificate instance (used only as a countermodel). -/
theorem certificate_instance : RouteCFunctionalCertificate 0 1 1 0 :=
  ⟨by norm_num, by norm_num, le_rfl⟩

/-- **The functional certificate does not construct the zeroth-moment contract.** -/
theorem certificate_does_not_give_S0 :
    RouteCFunctionalCertificate 0 1 1 0 ∧ ¬ S0Contract (fun _ => 0) (fun _ => 1) := by
  refine ⟨certificate_instance, fun h => ?_⟩
  obtain ⟨M₀, hM⟩ := h (1 / 2) (by norm_num)
  have := (hM M₀ le_rfl).2
  norm_num at this

/-- **The baseline provider is not vacuous.** -/
theorem baseline_provider_not_vacuous {V : Type} [Fintype V] [DecidableEq V]
    (τ : RouteCConsumer.FixedTupleC V) (W : RouteCConsumer.WeightSystem τ) :
    ¬ RouteCBaselineProvider τ W (fun _ => 0) (-100000) 0 :=
  baseline_provider_falsifiable τ W

/-- **The V14 effectivity firewall is unchanged in V16.** -/
theorem v16_effectivity_firewall (A : ℝ) :
    EffectivityFirewall.compilerUsefulHeightBound = none ∧
      EffectivityFirewall.explicitAnalyticThreshold = none ∧
      ResearchBankV11.AnalyticActivation.current_M_an A = none ∧
      EffectivityFirewall.finiteSpliceClosed = false ∧
      ResearchBankV13.AuditedEndpoint.concreteFinitePayload =
        ResearchBankV13.AuditedEndpoint.PayloadStatus.notSupplied :=
  EffectivityFirewall.effectivity_firewall A

end ScopeFirewalls
end ResearchBankV16
end Erdos287
