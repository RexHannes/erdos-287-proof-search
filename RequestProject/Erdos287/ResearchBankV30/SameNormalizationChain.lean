import RequestProject.Erdos287.ResearchBankV30.SameWeightChain

/-!
# Erdős #287 — Research Bank V30 §17: same normalization end to end

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`same_normalization_end_to_end` (LEAN CONDITIONAL): for ONE `R : RouteCNormalization`,
* S0 scale: `S0Contract (S0 τC W) R.N`;
* S1 scale: `S1Contract (S1 τC W) R.N μ_F`;
* principal scale: `pref Li phiW R.N M = Li M / (phiW · R.N M)`;
* pair baseline: `RouteCBaselineProvider τC W R.N W_F errFinal` (exact conversion
  `A_C W_F + 27/5 + η = A_C W_F + 90 + errFinal + η`, no asymptotic equivalence);
* actual pair: eventually `Pair/R.N ≤ A_C W_F + 27/5 + η`;
* score: the exact consumer check `ThinMarginCheck μ_lo W_hi errFinal`, which is what
  `conditional_asymptotic_287_of_baseline` consumes together with the three contracts at the SAME
  `R.N`.
-/

namespace Erdos287
namespace ResearchBankV30
namespace SameNormalizationChain

open ResearchBankV16.RouteCParameters ResearchBankV16.RouteCConsumer
open ResearchBankV16.ConditionalRouteCImplication
open ResearchBankV14.ConditionalAsymptoticImplication (S0Contract S1Contract)
open ResearchBankV17.ThinFunctional
open ResearchBankV23.PrincipalEuler ResearchBankV24.RepairedRouteCBaseline
open ResearchBankV27.DISpectral ResearchBankV28.RepairedAnalyticBundle
open ResearchBankV28.ExactParameterInstantiation
open ResearchBankV29.ProviderElimination ResearchBankV29.FunctionalCertificate
open ResearchBankV29.SourceNormalization

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The pair baseline from the full composition, with the exact constant conversion. -/
theorem baseline_of_full_pair {τC : FixedTupleC V} {W : WeightSystem τC} {N : ℕ → ℝ} {WF : ℝ}
    {Q : ℝ → ℕ → ℝ → ℕ → Prop}
    (h : ∀ η > 0, ∃ S : ℕ, ∃ τ : ℝ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      Q η S τ M ∧ Pair τC W M / N M ≤ ((A_C : ℚ) : ℝ) * WF + 27 / 5 + η) :
    RouteCBaselineProvider τC W N WF ((errFinal : ℚ) : ℝ) := by
  refine ⟨fun η hη => ?_⟩
  obtain ⟨_, _, M₀, hM₀⟩ := h η hη
  refine ⟨M₀, fun M hM => ?_⟩
  have herr : ((errFinal : ℚ) : ℝ) = -423 / 5 := by unfold errFinal; push_cast; ring
  rw [herr]; linarith [(hM₀ M hM).2]

/-- **Same normalization end to end** (LEAN CONDITIONAL). -/
theorem same_normalization_end_to_end (R : RouteCNormalization) {τC : FixedTupleC V}
    {W : WeightSystem τC} {K : ℕ} {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ}
    {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ} {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ}
    {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ} {Li : ℕ → ℝ} {phiW : ℝ}
    {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ} {Us Ur : ℕ → ℕ → Finset ℕ}
    {D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct Cnz : ℝ} {muF : ℝ}
    {DIClass : KloostermanData → Prop}
    (Mn : MinimalExternalAnalyticProviders τC W K h F Psm Prd lev X wτ r Sd LF I R.N Li phiW model
      Kh EAB Us Ur D0 D1 D2 Db muF DIClass)
    (C : FunctionalKernelCertificate muF (LF / I))
    (Gl : InternalGlueOwner τC W h E Psm Prd lev X wτ R.N Li phiW model EAB D0 D1 D2 Db DEnz Ct Cnz
      ((errFinal : ℚ) : ℝ) DIClass)
    (G : SieveGeometry E Psm Prd h model Us Ur) (cd : RoundedCellData Prd wτ X)
    (hLi : ∀ M, 0 ≤ Li M) (hphi : 0 < phiW) :
    S0Contract (S0 τC W) R.N ∧
    S1Contract (S1 τC W) R.N muF ∧
    (∀ M, pref Li phiW R.N M = Li M / (phiW * R.N M)) ∧
    RouteCBaselineProvider τC W R.N (LF / I) ((errFinal : ℚ) : ℝ) ∧
    (∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, Pair τC W M / R.N M ≤ ((A_C : ℚ) : ℝ) * (LF / I) + 27 / 5 + η) ∧
    ThinMarginCheck muLo WHi errFinal := by
  have hfull := FullPairComposition.full_pair_composition Mn C Gl G cd hLi hphi
  refine ⟨Mn.euler.normalization_agreement, Mn.s1, fun _ => rfl, baseline_of_full_pair hfull,
    fun η hη => ?_, thin_margin_check_final⟩
  obtain ⟨_, _, M₀, hM₀⟩ := hfull η hη
  exact ⟨M₀, fun M hM => (hM₀ M hM).2⟩

end SameNormalizationChain
end ResearchBankV30
end Erdos287
