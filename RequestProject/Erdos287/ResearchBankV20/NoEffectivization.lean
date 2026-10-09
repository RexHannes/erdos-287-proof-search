import RequestProject.Erdos287.ResearchBankV20.ConditionalAsymptotic287
import RequestProject.Erdos287.ResearchBankV17.ThinEffectivityFirewall
import RequestProject.Erdos287.ResearchBankV13.UpdatedSplice

/-!
# Erdős #287 — Research Bank V20: no effectivization

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `conditional_asymptotic_gives_no_explicit_M0` — an eventual conclusion `∃ M₀, ∀ M ≥ M₀, Q M`
  determines no explicit threshold: for every candidate `B` some eventually-true `Q` fails at `B`.
* `splice_needs_explicit_M0` — the finite/eventual splice closes the full statement only with an
  explicit `M_an ≤ U + 1` (positive direction, LEAN BANK from V13) and fails without a threshold
  (negative direction, V13 firewall).
* `v20_effectivity_status` — the V14 effectivity firewall is unchanged: no explicit analytic
  threshold, no closed finite splice.
-/

namespace Erdos287
namespace ResearchBankV20
namespace NoEffectivization

open ResearchBankV13.FiniteRepresentationModel ResearchBankV14

/-- **An eventual (conditional asymptotic) conclusion yields no explicit `M₀`.** -/
theorem conditional_asymptotic_gives_no_explicit_M0 (B : ℕ) :
    ∃ Q : ℕ → Prop, (∃ M₀ : ℕ, ∀ M ≥ M₀, Q M) ∧ ¬ ∀ M ≥ B, Q M :=
  ResearchBankV17.ThinEffectivityFirewall.eventual_gives_no_bound B

/-- **An explicit `M₀` is required before the finite splice can close #287.** -/
theorem splice_needs_explicit_M0 (U : ℕ) :
    (∀ M_an : ℕ, NoCounterexampleUpTo U → (∀ M, M_an ≤ M → NoCounterexampleAt M) →
        M_an ≤ U + 1 → ∀ A : Finset ℕ, ¬ Erdos287Counterexample A) ∧
    ¬ ∀ bad : ℕ → Prop, (∃ M₀, ∀ M ≥ M₀, ¬ bad M) → (∀ M ≤ U, ¬ bad M) → ∀ M, ¬ bad M :=
  ⟨fun _ hfin hev hU => ResearchBankV13.UpdatedSplice.erdos287_of_splice hfin hev hU,
   ResearchBankV13.UpdatedSplice.eventual_without_threshold_does_not_splice U⟩

/-- **The effectivity firewall is unchanged in V20.** -/
theorem v20_effectivity_status (A : ℝ) :
    EffectivityFirewall.compilerUsefulHeightBound = none ∧
      EffectivityFirewall.explicitAnalyticThreshold = none ∧
      ResearchBankV11.AnalyticActivation.current_M_an A = none ∧
      EffectivityFirewall.finiteSpliceClosed = false :=
  let h := EffectivityFirewall.effectivity_firewall A
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

end NoEffectivization
end ResearchBankV20
end Erdos287
