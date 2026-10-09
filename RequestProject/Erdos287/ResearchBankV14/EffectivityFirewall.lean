import RequestProject.Erdos287.ResearchBankV13
import RequestProject.Erdos287.ResearchBankV14.CompilerApplication

/-!
# Erdős #287 — Research Bank V14 §A11: effectivity firewall

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Encoded explicitly:

* `compilerUsefulHeightBound = none` — compiler existence is **not** a useful height bound;
  `compiler_outputs_unbounded` shows the existence theorem is compatible with arbitrarily large
  scales, so it carries no smallness information;
* `explicitAnalyticThreshold = none` — no explicit analytic threshold `M_an` is supplied (the V11
  value `current_M_an A = none` is re-used unchanged);
* `finiteSpliceClosed = false` — the finite splice is not closed;
* the externally audited `10^500` payload is still `notSupplied` (V13 value, unchanged); **no**
  theorem about it is introduced.
-/

namespace Erdos287
namespace ResearchBankV14
namespace EffectivityFirewall

open BalancedBlowup CompilerApplication

/-- No quantitatively useful compiler height bound is available. -/
def compilerUsefulHeightBound : Option ℕ := none

/-- No explicit analytic threshold is available. -/
def explicitAnalyticThreshold : Option ℕ := none

/-- The finite splice is not closed. -/
def finiteSpliceClosed : Bool := false

/-- **Compiler existence is not a height bound**: for every `B` the edge-only compiler admits
outputs of scale `≥ B`; existence alone says nothing about small outputs. -/
theorem compiler_outputs_unbounded (B : ℕ) :
    ∃ (T : ℕ) (b : Fin BalancedKernelParameters.K → ℤ), B ≤ T ∧
      (∀ v, lo v * T < b v ∧ (b v : ℚ) < hi v * T) ∧
      ∀ N : ℤ, ∃ A : ℤ, N ≤ A ∧
        ∀ u v, blowup.Adj u v → Int.gcd (A + b u) (A + b v) = (b u - b v).natAbs := by
  obtain ⟨T, b, -, hB, hbox, -, hA⟩ :=
    EdgeOnlyCompilerInterface.edgeOnly_compiler blowup lo hi lo_lt_hi B
  exact ⟨T, b, hB, hbox, hA⟩

/-- **The V14 effectivity firewall.** -/
theorem effectivity_firewall (A : ℝ) :
    compilerUsefulHeightBound = none ∧ explicitAnalyticThreshold = none ∧
      ResearchBankV11.AnalyticActivation.current_M_an A = none ∧ finiteSpliceClosed = false ∧
      ResearchBankV13.AuditedEndpoint.concreteFinitePayload =
        ResearchBankV13.AuditedEndpoint.PayloadStatus.notSupplied :=
  ⟨rfl, rfl, ResearchBankV13.EffectiveFrontier.current_M_an_none A, rfl, rfl⟩

end EffectivityFirewall
end ResearchBankV14
end Erdos287
