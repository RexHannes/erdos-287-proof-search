import RequestProject.Erdos287.ResearchBankV30.FinalPreEffectivity

/-!
# Erdős #287 — Research Bank V30 §21: trusted challenge statement

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

Plain statement file.  It contains only:
* the source definitions needed to read the statement, by reference:
  `Erdos287Counterexample` (ProblemStatement: finite set, ≥ 2 elements, all `> 1`, reciprocal sum
  `1`, gaps `≤ 2`), `NoCounterexampleAt` (V13), `MinimalExternalAnalyticProviders`,
  `FunctionalKernelCertificate`, `InternalGlueOwner` (V29);
* `TrustedStatement` — the closed proposition of `pre_effectivity_287_FINAL_BANK`;
* `trusted_challenge : TrustedStatement`, proved by the V30 theorem (no tactics beyond term
  application).
* `noCounterexampleAt_unfold` — `NoCounterexampleAt` literally unfolds to the #287 statement.

Comparator was not available in this environment (`comparator` is not on `PATH`, and
`lake comparator` is not a Lake command), so it was NOT run.
-/

namespace Erdos287
namespace ResearchBankV30
namespace TrustedChallenge

open ResearchBankV16.RouteCConsumer ResearchBankV13.FiniteRepresentationModel
open ResearchBankV23.PrincipalEuler ResearchBankV24.RepairedRouteCBaseline
open ResearchBankV27.DISpectral ResearchBankV28.ExactParameterInstantiation
open ResearchBankV29.ProviderElimination ResearchBankV29.FunctionalCertificate

/-- `NoCounterexampleAt M` unfolds to the literal #287 statement at endpoint `M`. -/
theorem noCounterexampleAt_unfold (M : ℕ) :
    NoCounterexampleAt M ↔ ∀ A : Finset ℕ, ∀ h : Erdos287Counterexample A, A.max' h.nonempty ≠ M :=
  Iff.rfl

/-- **The trusted statement.** -/
def TrustedStatement : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] {τC : FixedTupleC V} {W : WeightSystem τC} {K : ℕ}
    {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ} {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ}
    {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ} {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ}
    {N Li : ℕ → ℝ} {phiW : ℝ} {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ}
    {Us Ur : ℕ → ℕ → Finset ℕ} {D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct Cnz : ℝ}
    {muF : ℝ} {DIClass : KloostermanData → Prop},
    MinimalExternalAnalyticProviders τC W K h F Psm Prd lev X wτ r Sd LF I N Li phiW model
      Kh EAB Us Ur D0 D1 D2 Db muF DIClass →
    FunctionalKernelCertificate muF (LF / I) →
    InternalGlueOwner τC W h E Psm Prd lev X wτ N Li phiW model EAB D0 D1 D2 Db DEnz Ct Cnz
      ((errFinal : ℚ) : ℝ) DIClass →
    SieveGeometry E Psm Prd h model Us Ur → RoundedCellData Prd wτ X →
    (∀ M, 0 ≤ Li M) → 0 < phiW →
    ∃ M₀ : ℕ, ∀ M ≥ M₀, NoCounterexampleAt M

/-- **Trusted challenge, discharged.** -/
theorem trusted_challenge : TrustedStatement :=
  fun Mn C Gl G cd hLi hphi =>
    FinalPreEffectivity.pre_effectivity_287_FINAL_BANK Mn C Gl G cd hLi hphi

end TrustedChallenge
end ResearchBankV30
end Erdos287
