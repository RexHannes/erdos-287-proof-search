import RequestProject.Erdos287.ResearchBankV20.ConditionalThinPairTheorem

/-!
# Erdős #287 — Research Bank V20 §2: CONDITIONAL asymptotic reduction

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `conditional_asymptotic_287_of_baseline` (LEAN CONDITIONAL) — V15/V14 fixed-source S0/S1
  contracts + V16/V17 Route-C-thin consumer (thin functional certificate + exact margin check)
  + V14 compiler/harmonic infrastructure (inside the V16 consumer) + `ThinPairBaselineBound`
  ⟹ `∃ M₀, ∀ M ≥ M₀`, no counterexample has maximum `M`.
* `conditional_asymptotic_287_CONDITIONAL` (LEAN CONDITIONAL) — the same, with the baseline
  replaced by its providers (decomposition + local transport + the never-constructed
  `ActualCenteredSourceCompositionProvider`).

This is an ASYMPTOTIC CONDITIONAL REDUCTION.  It is NOT an explicit threshold, NOT a finite
splice, and NOT a global #287 theorem.
-/

namespace Erdos287
namespace ResearchBankV20
namespace ConditionalAsymptotic287

open ResearchBankV16.RouteCParameters ResearchBankV16.RouteCConsumer
open ResearchBankV17.ThinFunctional
open ResearchBankV19.BranchData ResearchBankV19.ActualCenteredCompositionProvider
open ResearchBankV13.FiniteRepresentationModel
open ResearchBankV14.ConditionalAsymptoticImplication (S0Contract S1Contract)
open ThinPairBaseline ConditionalThinPairTheorem

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Conditional asymptotic #287 from the thin pair baseline** (LEAN CONDITIONAL). -/
theorem conditional_asymptotic_287_of_baseline {muLo WHi err : ℚ} (τ : FixedTupleC V)
    (W : WeightSystem τ) (N : ℕ → ℝ) {muF WF : ℝ}
    (C : ThinFunctionalCertificate muLo WHi muF WF) (hchk : ThinMarginCheck muLo WHi err)
    (h0 : S0Contract (S0 τ W) N) (h1 : S1Contract (S1 τ W) N muF)
    (hB : ThinPairBaselineBound τ W N WF ((err : ℚ) : ℝ)) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, NoCounterexampleAt M :=
  ResearchBankV17.ThinConsumer.thin_eventually_no_counterexample τ W N C hchk h0 h1 hB

/-- **Conditional asymptotic #287 from all explicit providers** (LEAN CONDITIONAL).
`hC` is the OPEN `ActualCenteredSourceCompositionProvider`, never constructed in the bank. -/
theorem conditional_asymptotic_287_CONDITIONAL {muLo WHi err : ℚ} (τ : FixedTupleC V)
    (W : WeightSystem τ) (N : ℕ → ℝ) {muF WF : ℝ} (branches : List ActualBranchData)
    (C : ThinFunctionalCertificate muLo WHi muF WF) (hchk : ThinMarginCheck muLo WHi err)
    (h0 : S0Contract (S0 τ W) N) (h1 : S1Contract (S1 τ W) N muF)
    (hD : PairDecompositionProvider τ W N branches) (hT : LocalTransportBounds branches)
    (hC : ActualCenteredSourceCompositionProvider branches N
      (((A_C : ℚ) : ℝ) * WF + 90 + ((err : ℚ) : ℝ))) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, NoCounterexampleAt M :=
  conditional_asymptotic_287_of_baseline τ W N C hchk h0 h1
    (thinPairBaseline_of_providers_CONDITIONAL τ W N WF _ branches hD hT hC)

end ConditionalAsymptotic287
end ResearchBankV20
end Erdos287
