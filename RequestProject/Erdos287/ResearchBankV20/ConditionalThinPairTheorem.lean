import RequestProject.Erdos287.ResearchBankV20.ThinPairBaseline

/-!
# Erdős #287 — Research Bank V20 §1: the CONDITIONAL thin pair baseline theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**
**This is NOT a proved pair theorem.**

* `thinPairBaseline_of_providers_CONDITIONAL` (LEAN CONDITIONAL) —

      frozen standard analytic provider (`PairDecompositionProvider`)
      + V18/V19 local transport output (`LocalTransportBounds`)
      + `ActualCenteredSourceCompositionProvider` (OPEN — never constructed)
        with main constant `A_C W_F + 90 + err`
      ⟹ `ThinPairBaselineBound`.

The proof is the honest algebra: `Pair/N = Σ principal + (Σ err)/N`, the principal sum is at most
the main constant by `principalRecombination`, and `|Σ err| ≤ Σ localBound ≤ η N` eventually by
`localControl`.
-/

namespace Erdos287
namespace ResearchBankV20
namespace ConditionalThinPairTheorem

open ResearchBankV16.RouteCParameters ResearchBankV16.RouteCConsumer
open ResearchBankV16.ConditionalRouteCImplication
open ResearchBankV19.BranchData ResearchBankV19.ActualCenteredCompositionProvider
open ThinPairBaseline

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `|Σ err_b| ≤ Σ localBound_b` from the per-branch local transport bounds. -/
theorem err_sum_le (branches : List ActualBranchData) (hT : LocalTransportBounds branches)
    (M : ℕ) :
    |(branches.map fun b => b.err M).sum| ≤ (branches.map fun b => b.localBound M).sum := by
  have key : ∀ l : List ActualBranchData, (∀ b ∈ l, ∀ M, |b.err M| ≤ b.localBound M) →
      |(l.map fun b => b.err M).sum| ≤ (l.map fun b => b.localBound M).sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons b l ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      refine (abs_add_le _ _).trans (add_le_add (h b (List.mem_cons_self ..) M) ?_)
      exact ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb')
  exact key branches hT.local_bound

/-- **The conditional thin pair baseline** (LEAN CONDITIONAL; NOT a proved pair theorem). -/
theorem thinPairBaseline_of_providers_CONDITIONAL (τ : FixedTupleC V) (W : WeightSystem τ)
    (N : ℕ → ℝ) (WF err : ℝ) (branches : List ActualBranchData)
    (hD : PairDecompositionProvider τ W N branches) (hT : LocalTransportBounds branches)
    (hC : ActualCenteredSourceCompositionProvider branches N (((A_C : ℚ) : ℝ) * WF + 90 + err)) :
    ThinPairBaselineBound τ W N WF err := by
  refine ⟨fun η hη => ?_⟩
  obtain ⟨M₀, hM⟩ := hC.localControl η hη
  refine ⟨M₀, fun M hMM => ?_⟩
  obtain ⟨hN, hloc⟩ := hM M hMM
  have hE := (abs_le.1 ((err_sum_le branches hT M).trans hloc)).2
  rw [hD.decomp M, div_le_iff₀ hN]
  have hP := hC.principalRecombination
  nlinarith

end ConditionalThinPairTheorem
end ResearchBankV20
end Erdos287
