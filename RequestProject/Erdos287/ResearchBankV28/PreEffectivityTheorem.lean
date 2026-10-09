import RequestProject.Erdos287.ResearchBankV28.FinalPairComposition

/-!
# Erdős #287 — Research Bank V28 §13: the pre-effectivity asymptotic theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* **`pre_effectivity_asymptotic_287_after_full_repair`** (LEAN CONDITIONAL on
  `FinalAnalyticProviders` only, plus the structural sieve geometry / rounding data):

      FinalAnalyticProviders  ⟹  ∃ M₀, ∀ M ≥ M₀, no counterexample has maximum denominator M.

  It reuses the frozen S0 (from the principal provider's normalization field), S1, graph, score,
  compiler, contact, row rigidity and harmonic contradiction chain through
  `ResearchBankV20.ConditionalAsymptotic287.conditional_asymptotic_287_of_baseline`, with the
  exact final margin check `thin_margin_check_final` at `err = −423/5`.

This theorem is NOT the global Erdős #287: `M₀` is only asserted to exist (it may depend on
ineffective analytic constants), no explicit `M₀` is produced, and the finite splice is not
performed.
-/

namespace Erdos287
namespace ResearchBankV28
namespace PreEffectivityTheorem

open ResearchBankV16.RouteCConsumer
open ResearchBankV13.FiniteRepresentationModel
open ResearchBankV23.PrincipalEuler
open ResearchBankV24.RepairedRouteCBaseline
open RepairedAnalyticBundle FinalPairComposition ExactParameterInstantiation

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Pre-effectivity asymptotic #287 after the full repair** (LEAN CONDITIONAL). -/
theorem pre_effectivity_asymptotic_287_after_full_repair {τC : FixedTupleC V}
    {W : WeightSystem τC} {K : ℕ} {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ}
    {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ} {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ}
    {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ} {N Li : ℕ → ℝ} {phiW : ℝ}
    {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ} {Us Ur : ℕ → ℕ → Finset ℕ}
    {D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct Cnz : ℝ} {muF : ℝ}
    {DIClass : ResearchBankV27.DISpectral.KloostermanData → Prop}
    (B : FinalAnalyticProviders τC W K h F E Psm Prd lev X wτ r Sd LF I N Li phiW model Kh EAB
      Us Ur D0 D1 D2 Db DEnz Ct Cnz ((errFinal : ℚ) : ℝ) muLo WHi muF DIClass)
    (G : SieveGeometry E Psm Prd h model Us Ur) (cd : RoundedCellData Prd wτ X)
    (hLi : ∀ M, 0 ≤ Li M) (hphi : 0 < phiW) (hWF : 0 ≤ LF / I) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, NoCounterexampleAt M :=
  ResearchBankV20.ConditionalAsymptotic287.conditional_asymptotic_287_of_baseline τC W N B.cert
    thin_margin_check_final B.euler.normalization_agreement B.s1
    (routeC_pair_baseline_after_full_repair B G cd hLi hphi hWF)

end PreEffectivityTheorem
end ResearchBankV28
end Erdos287
