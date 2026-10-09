import Mathlib.Tactic
import RequestProject.Erdos287.ResearchBankV15.FirstMomentContract
import RequestProject.Erdos287.ResearchBankV15.PairProvider

/-!
# Erdős #287 — Research Bank V15 §B12: the one-lemma asymptotic reduction

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

* `StandardProviders src muF` — the named standard fixed-source analytic providers:
  the `S0` main-term (Mellin / Euler, collision singular factors) provider, the divisor-moment
  provider, the Bombieri–Vinogradov transfer, and the `S1` main-term provider;
* `one_lemma_reduction` —

      OrdinaryBVProvider + StandardProviders + ActualWeightedColouredPairProvider
        ⟹ no #287 counterexample with maximum M, for every sufficiently large M;

* `open_content_concentrated` — once the ordinary BV provider and the standard providers are
  granted, the **only** remaining hypothesis is `ActualWeightedColouredPairProvider`.

"One-lemma reduction" means one remaining **new** asymptotic provider in this architecture.  It
does **not** mean the provider is known, nor that it follows from Pascadi (see `ScopeFirewalls`).
-/

namespace Erdos287
namespace ResearchBankV15
namespace OneLemmaReduction

open ResearchBankV13.FiniteRepresentationModel
open ResearchBankV14 ResearchBankV14.BalancedKernelParameters
open ResearchBankV14.ConditionalAsymptoticImplication
open FixedAffineSource Normalization ZerothMomentContract FirstMomentContract PairProvider
open BombieriVinogradovProvider

/-- The named standard fixed-source analytic providers. -/
structure StandardProviders (src : SourceData) (muF : ℝ) : Prop where
  s0Main : S0MainTermProvider src
  divisor : DivisorMomentProvider src
  bvTransfer : BVTransfer src
  s1Main : S1MainTermProvider src muF

/-- **The one-lemma asymptotic reduction.** -/
theorem one_lemma_reduction (B : CertifiedFunctionalBounds) (src : SourceData)
    (bv : OrdinaryBVProvider) (std : StandardProviders src B.muF)
    (hP : PairProvider.ActualWeightedColouredPairProvider src B.WF) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, NoCounterexampleAt M :=
  eventually_no_counterexample tuple (weightSystem src) (NX src) B
    (s0_contract src std.s0Main std.divisor) (s1_contract src bv std.bvTransfer std.s1Main)
    (toV14 src hP)

/-- **All remaining open analytic content is concentrated in the pair provider.** -/
theorem open_content_concentrated (B : CertifiedFunctionalBounds) (src : SourceData)
    (bv : OrdinaryBVProvider) (std : StandardProviders src B.muF) :
    PairProvider.ActualWeightedColouredPairProvider src B.WF →
      ∃ M₀ : ℕ, ∀ M ≥ M₀, NoCounterexampleAt M :=
  one_lemma_reduction B src bv std

/-- The contracts produced on the way (both conditional on the named providers). -/
theorem contracts_of_providers (B : CertifiedFunctionalBounds) (src : SourceData)
    (bv : OrdinaryBVProvider) (std : StandardProviders src B.muF) :
    S0Contract (S0 tuple (weightSystem src)) (NX src) ∧
      S1Contract (S1 tuple (weightSystem src)) (NX src) B.muF :=
  ⟨s0_contract src std.s0Main std.divisor, s1_contract src bv std.bvTransfer std.s1Main⟩

end OneLemmaReduction
end ResearchBankV15
end Erdos287
