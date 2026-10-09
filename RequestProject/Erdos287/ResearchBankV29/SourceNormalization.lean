import RequestProject.Erdos287.ResearchBankV29.TwoLargeComposition
import RequestProject.Erdos287.ResearchBankV28.FinalPairComposition

/-!
# Erdős #287 — Research Bank V29 §8–§9: one normalization, one auxiliary weight

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## §8 `RouteCNormalization`

`RouteCNormalization` wraps ONE function `N : ℕ → ℝ`.  `all_components_same_normalization` proves,
from the V28 bundle instantiated at `R.N`, that the SAME `R.N` (no shadow copy) is the
normalization of:
* `S0` — `S0Contract (S0 τC W) R.N` (the principal provider's `normalization_agreement` field);
* `S1` — `S1Contract (S1 τC W) R.N μ_F`;
* the principal term — `pref Li phiW R.N M = Li M / (phiW · R.N M)`;
* the pair norm / actual-measure transfer — the tensor decomposition bounds `Pair/R.N`;
* the score consumer — `RouteCBaselineProvider τC W R.N (LF/I) err`, the exact object consumed by
  `ResearchBankV20.ConditionalAsymptotic287.conditional_asymptotic_287_of_baseline`.

## §9 `LambdaNewPlus`

`principal_weight_eq_error_weight`: the weight in the principal term, in the source-branch
remainder `DE_src`, in the nonzero remainder `DE_nz`, and in the V24 source decomposition is the
ONE family `LamFam E Psm Prd lev X wτ S τ M`, which is DEFINITIONALLY the V22
`LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M)` (no factorable proxy).  The proof is
the tensor decomposition re-stated with `LambdaNewPlus` substituted in every slot — it type-checks
only because all slots carry the same weight.

Both results are LEAN BANK / LEAN CONDITIONAL on the bundle only through projections.
-/

namespace Erdos287
namespace ResearchBankV29
namespace SourceNormalization

open ResearchBankV22.CompletedPositiveWeight
open ResearchBankV23.PrincipalEuler
open ResearchBankV16.RouteCConsumer ResearchBankV16.ConditionalRouteCImplication
open ResearchBankV14.ConditionalAsymptoticImplication (S0Contract S1Contract)
open ResearchBankV24.RepairedRouteCBaseline
open ResearchBankV28.RepairedAnalyticBundle ResearchBankV28.FinalPairComposition

/-- **The one canonical Route-C normalization** `N_x`. -/
structure RouteCNormalization where
  N : ℕ → ℝ

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **All components use the same normalization** (LEAN CONDITIONAL, projections of the bundle). -/
theorem all_components_same_normalization (R : RouteCNormalization) {τC : FixedTupleC V}
    {W : WeightSystem τC} {K : ℕ} {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ}
    {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ} {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ}
    {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ} {Li : ℕ → ℝ} {phiW : ℝ}
    {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ} {Us Ur : ℕ → ℕ → Finset ℕ}
    {D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct Cnz err : ℝ} {muLo WHi : ℚ} {muF : ℝ}
    {DIClass : ResearchBankV27.DISpectral.KloostermanData → Prop}
    (B : FinalAnalyticProviders τC W K h F E Psm Prd lev X wτ r Sd LF I R.N Li phiW model Kh EAB
      Us Ur D0 D1 D2 Db DEnz Ct Cnz err muLo WHi muF DIClass)
    (G : SieveGeometry E Psm Prd h model Us Ur) (cd : RoundedCellData Prd wτ X)
    (hLi : ∀ M, 0 ≤ Li M) (hphi : 0 < phiW) (hWF : 0 ≤ LF / I) :
    S0Contract (S0 τC W) R.N ∧
    S1Contract (S1 τC W) R.N muF ∧
    (∀ M, pref Li phiW R.N M = Li M / (phiW * R.N M)) ∧
    (∀ S τ M, Pair τC W M / R.N M ≤
      (model S M).Mnew (pref Li phiW R.N M) (LamFam E Psm Prd lev X wτ S τ M) +
        |sumDE D0 D1 D2 Db M (LamFam E Psm Prd lev X wτ S τ M)| +
        max (DEnz M (LamFam E Psm Prd lev X wτ S τ M)) 0 + Ct * Real.sqrt |EAB M| + 90 + err) ∧
    RouteCBaselineProvider τC W R.N (LF / I) err :=
  ⟨B.euler.normalization_agreement, B.s1, fun _ => rfl, B.tensor.decomp,
    routeC_pair_baseline_after_full_repair B G cd hLi hphi hWF⟩

/-- `LamFam` IS `LambdaNewPlus` (LEAN BANK, definitional). -/
theorem lamFam_eq_lambdaNewPlus (E : Finset ℕ) (Psm Prd : ℕ → ℝ → Finset ℕ) (lev X : ℝ → ℝ)
    (wτ : ℝ → ℝ → ℕ → ℝ) (S : ℕ) (τ : ℝ) (M : ℕ) :
    LamFam E Psm Prd lev X wτ S τ M =
      LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M) := rfl

/-- **The principal weight is the error weight** (LEAN CONDITIONAL, projection of the bundle):
the tensor decomposition with `LambdaNewPlus` in the principal, `DE_src` and `DE_nz` slots. -/
theorem principal_weight_eq_error_weight {τC : FixedTupleC V}
    {W : WeightSystem τC} {K : ℕ} {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ}
    {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ} {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ}
    {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ} {N Li : ℕ → ℝ} {phiW : ℝ}
    {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ} {Us Ur : ℕ → ℕ → Finset ℕ}
    {D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct Cnz err : ℝ} {muLo WHi : ℚ} {muF : ℝ}
    {DIClass : ResearchBankV27.DISpectral.KloostermanData → Prop}
    (B : FinalAnalyticProviders τC W K h F E Psm Prd lev X wτ r Sd LF I N Li phiW model Kh EAB
      Us Ur D0 D1 D2 Db DEnz Ct Cnz err muLo WHi muF DIClass) (S : ℕ) (τ : ℝ) (M : ℕ) :
    Pair τC W M / N M ≤
      (model S M).Mnew (pref Li phiW N M)
          (LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M)) +
        |sumDE D0 D1 D2 Db M (LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M))| +
        max (DEnz M (LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M))) 0 +
        Ct * Real.sqrt |EAB M| + 90 + err :=
  B.tensor.decomp S τ M

end SourceNormalization
end ResearchBankV29
end Erdos287
