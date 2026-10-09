import RequestProject.Erdos287.ResearchBankV30.SameSourceChain

/-!
# Erdős #287 — Research Bank V30 §16: same auxiliary weight end to end

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`same_auxiliary_weight_end_to_end` (LEAN CONDITIONAL): for every `η > 0` there are `S, τ, M₀`
such that for `M ≥ M₀`, with the ONE weight
`Λ = LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M)`:
* (physical upper majorant = remainder) the glue owner's actual-measure majorization of `Pair/N`
  holds with `Λ` in the principal slot, the source-branch remainder slot and the nonzero slot;
* (principal evaluation) the same-weight principal bound `M_new(Λ) ≤ A_C W_F + η` holds for the
  SAME `Λ` (same `S, τ, M`);
* `Λ` has a V24 source decomposition (the weight consumed by the branch class bounds).

The statement literally substitutes `LambdaNewPlus` in every slot; it type-checks because
`LamFam … S τ M` is definitionally that weight (`lamFam_eq_lambdaNewPlus`).
-/

namespace Erdos287
namespace ResearchBankV30
namespace SameWeightChain

open ResearchBankV22.CompletedPositiveWeight
open ResearchBankV16.RouteCParameters ResearchBankV16.RouteCConsumer
open ResearchBankV23.PrincipalEuler ResearchBankV23.PrincipalBudget
open ResearchBankV24.RepairedProvider ResearchBankV24.RepairedRouteCBaseline
open ResearchBankV27.DISpectral ResearchBankV28.RepairedAnalyticBundle
open ResearchBankV29.ProviderElimination ResearchBankV29.FunctionalCertificate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Same auxiliary weight end to end** (LEAN CONDITIONAL). -/
theorem same_auxiliary_weight_end_to_end {τC : FixedTupleC V} {W : WeightSystem τC} {K : ℕ}
    {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ} {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ}
    {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ} {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ}
    {N Li : ℕ → ℝ} {phiW : ℝ} {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ}
    {Us Ur : ℕ → ℕ → Finset ℕ} {D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct Cnz err : ℝ}
    {muF : ℝ} {DIClass : KloostermanData → Prop}
    (Mn : MinimalExternalAnalyticProviders τC W K h F Psm Prd lev X wτ r Sd LF I N Li phiW model
      Kh EAB Us Ur D0 D1 D2 Db muF DIClass)
    (C : FunctionalKernelCertificate muF (LF / I))
    (Gl : InternalGlueOwner τC W h E Psm Prd lev X wτ N Li phiW model EAB D0 D1 D2 Db DEnz Ct Cnz
      err DIClass)
    (G : SieveGeometry E Psm Prd h model Us Ur) (cd : RoundedCellData Prd wτ X)
    (hLi : ∀ M, 0 ≤ Li M) (hphi : 0 < phiW) :
    ∀ η > 0, ∃ S : ℕ, ∃ τ : ℝ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      (Pair τC W M / N M ≤
        (model S M).Mnew (pref Li phiW N M)
            (LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M)) +
          |sumDE D0 D1 D2 Db M (LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M))| +
          max (DEnz M (LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M))) 0 +
          Ct * Real.sqrt |EAB M| + 90 + err) ∧
      (model S M).Mnew (pref Li phiW N M)
          (LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M)) ≤
        ((A_C : ℚ) : ℝ) * (LF / I) + η ∧
      SourceDecomposition (LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M))
        (Us S M) (Ur S M) ((((cd.R S τ + 1) ^ cd.nC S τ : ℕ) : ℝ) * 3 ^ cd.R S τ) := by
  intro η hη
  obtain ⟨S, -, τ, -, M1, hM1⟩ := principal_budget_le_A_C Mn.rosser Mn.tuple Mn.euler G.hU G.d1
    G.d2 G.d3 G.hh hLi hphi C.WF_nonneg η hη
  refine ⟨S, τ, M1, fun M hM => ⟨Gl.tensor.decomp S τ M, hM1 M hM, ?_⟩⟩
  rw [G.hUs, G.hUr]
  exact lamFam_source_decomposition cd G.d1 G.d2 G.d3 S τ M

end SameWeightChain
end ResearchBankV30
end Erdos287
