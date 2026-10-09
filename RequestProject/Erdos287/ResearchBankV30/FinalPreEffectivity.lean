import RequestProject.Erdos287.ResearchBankV30.QuantifierOrder

/-!
# Erdős #287 — Research Bank V30 §19: the final pre-effectivity theorem

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**
**Explicit `M₀` is OPEN.  Finite splice is OPEN.**

`pre_effectivity_287_FINAL_BANK` (LEAN CONDITIONAL):

    MinimalExternalAnalyticProviders  (EXTERNAL analytic inputs only)
    → FunctionalKernelCertificate     (FINITE CERTIFIED INPUT)
    → InternalGlueOwner               (INTERNAL composition obligation — NOT eliminated)
    → structural sieve geometry / rounded cell data / Li ≥ 0 / φ(W) > 0
    → ∃ M₀, ∀ M ≥ M₀, NoCounterexampleAt M.

**Classification: this is NOT "SUCCESS A".**  The theorem still depends on the internal glue
owner (actual-measure majorization with physically defined branch functionals + clean
realization of the nonzero branch, including DIClass membership and the pruning contract), and on
the structural hypotheses about the uninterpreted sieve universes.  See `Status` and the V30
report: the outcome is SUCCESS D (same-source chain not established; first mismatch at the
zero-frequency functional `D0`), with the internal residue isolated in ONE named structure.

The chain: `full_pair_composition` → `baseline_of_full_pair` (exact `27/5 = 90 + errFinal`) →
`ResearchBankV20.ConditionalAsymptotic287.conditional_asymptotic_287_of_baseline` with the frozen
thin certificate (from `FunctionalKernelCertificate`), `thin_margin_check_final`, the principal
provider's `S0Contract` and the `S1Contract` — all at the SAME `N`.
-/

namespace Erdos287
namespace ResearchBankV30
namespace FinalPreEffectivity

open ResearchBankV16.RouteCConsumer ResearchBankV13.FiniteRepresentationModel
open ResearchBankV23.PrincipalEuler ResearchBankV24.RepairedRouteCBaseline
open ResearchBankV27.DISpectral ResearchBankV28.ExactParameterInstantiation
open ResearchBankV29.ProviderElimination ResearchBankV29.FunctionalCertificate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The pre-effectivity #287 research-bank theorem** (LEAN CONDITIONAL; see classification). -/
theorem pre_effectivity_287_FINAL_BANK {τC : FixedTupleC V} {W : WeightSystem τC} {K : ℕ}
    {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ} {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ}
    {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ} {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ}
    {N Li : ℕ → ℝ} {phiW : ℝ} {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ}
    {Us Ur : ℕ → ℕ → Finset ℕ} {D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct Cnz : ℝ}
    {muF : ℝ} {DIClass : KloostermanData → Prop}
    (Mn : MinimalExternalAnalyticProviders τC W K h F Psm Prd lev X wτ r Sd LF I N Li phiW model
      Kh EAB Us Ur D0 D1 D2 Db muF DIClass)
    (C : FunctionalKernelCertificate muF (LF / I))
    (Gl : InternalGlueOwner τC W h E Psm Prd lev X wτ N Li phiW model EAB D0 D1 D2 Db DEnz Ct Cnz
      ((errFinal : ℚ) : ℝ) DIClass)
    (G : SieveGeometry E Psm Prd h model Us Ur) (cd : RoundedCellData Prd wτ X)
    (hLi : ∀ M, 0 ≤ Li M) (hphi : 0 < phiW) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, NoCounterexampleAt M :=
  ResearchBankV20.ConditionalAsymptotic287.conditional_asymptotic_287_of_baseline τC W N
    ((certificate_iff_thin muF (LF / I)).1 C) thin_margin_check_final
    Mn.euler.normalization_agreement Mn.s1
    (SameNormalizationChain.baseline_of_full_pair
      (FullPairComposition.full_pair_composition Mn C Gl G cd hLi hphi))

end FinalPreEffectivity
end ResearchBankV30
end Erdos287
