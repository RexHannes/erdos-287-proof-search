import RequestProject.Erdos287.ResearchBankV16.RouteCConsumer
import RequestProject.Erdos287.ResearchBankV16.RelaxedPairBudget
import RequestProject.Erdos287.ResearchBankV14.ConditionalAsymptoticImplication

/-!
# Erdős #287 — Research Bank V16 §6: the conditional Route-C consumer

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `RouteCBaselineProvider τ W N W_F err` — the exact contract needed for the Route-C pair bound:
  for the SAME fixed Route-C tuple, SAME nonnegative weight, SAME proportional window and SAME
  normalization `N`, eventually `Pair/N ≤ A_C W_F + 90 + err + η` for every `η > 0`.
  **Defined, never constructed** (OPEN).
* `routeC_eventually_no_counterexample` (LEAN CONDITIONAL) —

      fixed-source S0/S1 contracts (V14 `S0Contract`, `S1Contract`)
      + RouteCBaselineProvider
      + Route-C functional certificate and exact margin check
      + compiler tuple / contact localization / rigidity / harmonic infrastructure
      ⟹ no counterexample with maximum `M`, for all sufficiently large `M`.

The conclusion is asymptotic (`∃ M₀, ∀ M ≥ M₀`); no explicit `M₀` is produced.
-/

namespace Erdos287
namespace ResearchBankV16
namespace ConditionalRouteCImplication

open RouteCParameters RouteCConsumer RelaxedPairBudget Score26
open ResearchBankV13.FiniteRepresentationModel
open ResearchBankV14.ConditionalAsymptoticImplication (S0Contract S1Contract)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The Route-C baseline provider** (OPEN; never constructed in the bank). -/
structure RouteCBaselineProvider (τ : FixedTupleC V) (W : WeightSystem τ) (N : ℕ → ℝ)
    (WF err : ℝ) : Prop where
  eventual : ∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
    Pair τ W M / N M ≤ ((A_C : ℚ) : ℝ) * WF + 90 + err + η

/-- **The conditional Route-C implication** (LEAN CONDITIONAL on the explicit providers). -/
theorem routeC_eventually_no_counterexample {muLo WHi err : ℚ} (τ : FixedTupleC V)
    (W : WeightSystem τ) (N : ℕ → ℝ) {muF WF : ℝ}
    (C : RouteCFunctionalCertificate muLo WHi muF WF) (hchk : RouteCMarginCheck muLo WHi err)
    (h0 : S0Contract (S0 τ W) N) (h1 : S1Contract (S1 τ W) N muF)
    (hP : RouteCBaselineProvider τ W N WF ((err : ℚ) : ℝ)) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, NoCounterexampleAt M := by
  have hm := routeC_margin_pos C hchk
  obtain ⟨Mp, hpos⟩ := eventual_score_positive (S0 τ W) (S1 τ W) (Pair τ W) N hm
    (fun η hη => by
      obtain ⟨M₀, h⟩ := h0 η hη
      refine ⟨M₀, fun M hM => ?_⟩
      obtain ⟨hN, habs⟩ := h M hM
      refine ⟨hN, ?_⟩
      have := (abs_le.1 habs).2
      have h' : S0 τ W M / N M ≤ 1 + η := by linarith
      rwa [div_le_iff₀ hN] at h')
    (fun η hη => by
      obtain ⟨M₀, h⟩ := h1 η hη
      obtain ⟨M₁, h'⟩ := h0 1 one_pos
      refine ⟨max M₀ M₁, fun M hM => ?_⟩
      have hN := (h' M (le_trans (le_max_right _ _) hM)).1
      exact (le_div_iff₀ hN).1 (h M (le_trans (le_max_left _ _) hM)))
    (fun η hη => by
      obtain ⟨M₀, h⟩ := hP.eventual η hη
      obtain ⟨M₁, h'⟩ := h0 1 one_pos
      refine ⟨max M₀ M₁, fun M hM => ?_⟩
      have hN := (h' M (le_trans (le_max_right _ _) hM)).1
      exact (div_le_iff₀ hN).1 (h M (le_trans (le_max_left _ _) hM)))
  obtain ⟨Mw, hw⟩ := window_good τ
  refine ⟨max Mp Mw, fun M hM => ?_⟩
  have hs := hpos M (le_trans (le_max_left _ _) hM)
  have hgood := hw M (le_trans (le_max_right _ _) hM)
  have hsum : 0 < ∑ t ∈ window τ M, W.w M t * (scoreR τ t - 350) := by
    rw [score_identity]; exact hs
  obtain ⟨t, ht, -, hS⟩ :=
    Score26.exists_gt_of_weighted_pos _ _ _ (fun t _ => W.w_nonneg M t) hsum
  obtain ⟨hrig, hcon⟩ := hgood t ht
  exact no_counterexample_of_good_t τ hrig hcon hS

/-- The Route-C baseline provider is a genuine, falsifiable proposition: with `N ≡ 0` and a very
negative `W_F` it fails (so it cannot be satisfied vacuously). -/
theorem baseline_provider_falsifiable (τ : FixedTupleC V) (W : WeightSystem τ) :
    ¬ RouteCBaselineProvider τ W (fun _ => 0) (-100000) 0 := by
  intro h
  obtain ⟨M₀, hM⟩ := h.eventual 1 one_pos
  have := hM M₀ le_rfl
  simp only [div_zero] at this
  have hA : ((A_C : ℚ) : ℝ) = 1000273 / 273000 := by unfold A_C; push_cast; ring
  rw [hA] at this
  norm_num at this

end ConditionalRouteCImplication
end ResearchBankV16
end Erdos287
