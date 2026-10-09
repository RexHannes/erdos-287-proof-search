import RequestProject.Erdos287.ResearchBankV17.ThinConsumer
import RequestProject.Erdos287.ResearchBankV19.ActualCenteredCompositionProvider

/-!
# Erdős #287 — Research Bank V20 §1: the thin pair baseline (definitions)

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `ThinPairBaselineBound τ W N W_F err` — the pair-baseline bound consumed by the Route-C-thin
  consumer: definitionally the V16 `RouteCBaselineProvider` contract (same tuple, same weight,
  same normalization; eventually `Pair/N ≤ A_C W_F + 90 + err + η` for every `η > 0`).
  **Not constructed anywhere in the bank.**
* `PairDecompositionProvider τ W N branches` — the frozen standard analytic input (EXTERNAL
  PROVIDER shape: Heath-Brown identity + dispersion bookkeeping): the actual weighted pair count
  decomposes EXACTLY as `N(M) · Σ_b principal_b + Σ_b err_b(M)` over the actual branch list.
* `thinPairBaselineBound_iff` — the baseline bound is literally the Route-C provider.
* `decomposition_provider_falsifiable` — the decomposition provider is a genuine proposition.
-/

namespace Erdos287
namespace ResearchBankV20
namespace ThinPairBaseline

open ResearchBankV16.RouteCParameters ResearchBankV16.RouteCConsumer
open ResearchBankV16.ConditionalRouteCImplication
open ResearchBankV19.BranchData

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The thin pair baseline bound** (the V16 Route-C baseline contract; never constructed). -/
def ThinPairBaselineBound (τ : FixedTupleC V) (W : WeightSystem τ) (N : ℕ → ℝ) (WF err : ℝ) :
    Prop :=
  RouteCBaselineProvider τ W N WF err

theorem thinPairBaselineBound_iff (τ : FixedTupleC V) (W : WeightSystem τ) (N : ℕ → ℝ)
    (WF err : ℝ) :
    ThinPairBaselineBound τ W N WF err ↔
      ∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, Pair τ W M / N M ≤ ((A_C : ℚ) : ℝ) * WF + 90 + err + η :=
  ⟨fun h => h.eventual, fun h => ⟨h⟩⟩

/-- **Frozen standard analytic provider** (EXTERNAL PROVIDER shape): exact branch decomposition
of the actual weighted pair count. -/
structure PairDecompositionProvider (τ : FixedTupleC V) (W : WeightSystem τ) (N : ℕ → ℝ)
    (branches : List ActualBranchData) : Prop where
  decomp : ∀ M, Pair τ W M =
    N M * (branches.map fun b => b.principal).sum + (branches.map fun b => b.err M).sum

/-- The decomposition provider is falsifiable: with no branches it forces `Pair ≡ 0`, which
fails as soon as some pair count is nonzero. -/
theorem decomposition_provider_falsifiable (τ : FixedTupleC V) (W : WeightSystem τ)
    (N : ℕ → ℝ) (M : ℕ) (hM : Pair τ W M ≠ 0) : ¬ PairDecompositionProvider τ W N [] := by
  intro h
  have := h.decomp M
  simp at this
  exact hM this

end ThinPairBaseline
end ResearchBankV20
end Erdos287
