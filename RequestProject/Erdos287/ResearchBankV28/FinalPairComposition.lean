import RequestProject.Erdos287.ResearchBankV28.RepairedAnalyticBundle

/-!
# Erdős #287 — Research Bank V28 §12: end-to-end pair composition

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**
**This is NOT a proved pair theorem: it is LEAN CONDITIONAL on `FinalAnalyticProviders`.**

The composition uses, for ONE and the SAME completed weight `Λ = LamFam S τ M` (V24):
1. the completed positive sieve and its coefficient contract (`lamFam_source_decomposition`,
   V24 LEAN BANK);
2./3. the zero-frequency (masked SW / BDH, V25 localization), one-large, two-large and
   product-boundary (V26) branch class bounds, combined through the DERIVED source-class provider;
4. the V27 DERIVED clean-nonzero theorem (`nonzero_branch_small`);
5./6. the zero-frequency and one-large / two-large branches (inside `sumDE`);
7. the V23 same-weight principal budget `principal_budget_le_A_C`;
8. the actual tensor approximation (`hat_approximation_eventually_small`).
No auxiliary weight changes between error and principal; the normalization `N` is the frozen one.

* **`routeC_pair_baseline_after_full_repair`** — the frozen V16 `RouteCBaselineProvider`:
  eventually `Pair/N ≤ A_C W_F + 90 + err + η`.
* `bx_norm_bound` — the non-off-principal part `‖B_x‖²_ν := M_new + |DE_src| + [DE_nz]_+ +
  C_t √|E_AB|` is eventually `≤ A_C W_F + η` (i.e. `A_C W_F + o(1)`).
* `pair_ratio_final` — at `err = −423/5`: eventually `P_actual/N ≤ A_C W_F + 27/5 + η`.
-/

namespace Erdos287
namespace ResearchBankV28
namespace FinalPairComposition

open Finset
open ResearchBankV22.RosserCostProvider
open ResearchBankV23.PrincipalEuler ResearchBankV23.HatApproximationProvider
open ResearchBankV23.PrincipalBudget
open ResearchBankV16.RouteCParameters ResearchBankV16.RouteCConsumer
open ResearchBankV16.ConditionalRouteCImplication
open ResearchBankV24.RepairedProvider ResearchBankV24.RepairedRouteCBaseline
open RepairedAnalyticBundle

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The non-off-principal part of the pair bound for the SAME weight. -/
noncomputable def BxSq {h : ℕ → ℝ} (model : ℕ → ℕ → PrincipalModel h) (pref : ℕ → ℝ)
    (Λ : ℕ → ℝ → ℕ → Finset ℕ → ℝ) (DEsrc DEnz : ℕ → (Finset ℕ → ℝ) → ℝ) (EAB : ℕ → ℝ)
    (Ct : ℝ) (S : ℕ) (τ : ℝ) (M : ℕ) : ℝ :=
  (model S M).Mnew (pref M) (Λ S τ M) + |DEsrc M (Λ S τ M)| + max (DEnz M (Λ S τ M)) 0 +
    Ct * Real.sqrt |EAB M|

/-- **`‖B_x‖² ≤ A_C W_F + o(1)`** (LEAN CONDITIONAL on `FinalAnalyticProviders`). -/
theorem bx_norm_bound {τC : FixedTupleC V} {W : WeightSystem τC} {K : ℕ} {h : ℕ → ℝ}
    {F : ℝ → ℝ} {E : Finset ℕ} {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ}
    {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ} {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ}
    {N Li : ℕ → ℝ} {phiW : ℝ} {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ}
    {Us Ur : ℕ → ℕ → Finset ℕ} {D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct Cnz err : ℝ}
    {muLo WHi : ℚ} {muF : ℝ} {DIClass : ResearchBankV27.DISpectral.KloostermanData → Prop}
    (B : FinalAnalyticProviders τC W K h F E Psm Prd lev X wτ r Sd LF I N Li phiW model Kh EAB
      Us Ur D0 D1 D2 Db DEnz Ct Cnz err muLo WHi muF DIClass)
    (G : SieveGeometry E Psm Prd h model Us Ur) (cd : RoundedCellData Prd wτ X)
    (hLi : ∀ M, 0 ≤ Li M) (hphi : 0 < phiW) (hWF : 0 ≤ LF / I) :
    ∀ η > 0, ∃ S : ℕ, ∃ τ : ℝ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      BxSq model (pref Li phiW N) (LamFam E Psm Prd lev X wτ) (sumDE D0 D1 D2 Db) DEnz EAB Ct
        S τ M ≤ ((A_C : ℚ) : ℝ) * (LF / I) + η := by
  intro η hη
  -- 7. same-weight principal (V23)
  obtain ⟨S, -, τ, -, M1, hM1⟩ := principal_budget_le_A_C B.rosser B.tuple B.euler G.hU G.d1 G.d2
    G.d3 G.hh hLi hphi hWF (η / 4) (by positivity)
  -- 1.–3., 5., 6. source branches via the DERIVED source-class provider
  have Psrc := derived_source_class_provider B.zeroFreq B.oneLarge B.twoLarge B.boundary
  set Cm : ℝ := (((cd.R S τ + 1) ^ cd.nC S τ : ℕ) : ℝ) * 3 ^ cd.R S τ
  have hCm : 0 ≤ Cm := by positivity
  have hdec : ∀ M, SourceDecomposition (LamFam E Psm Prd lev X wτ S τ M) (Us S M) (Ur S M) Cm := by
    intro M
    rw [G.hUs, G.hUr]
    exact lamFam_source_decomposition cd G.d1 G.d2 G.d3 S τ M
  obtain ⟨M2, hM2⟩ := distribution_error_small Psrc S (LamFam E Psm Prd lev X wτ S τ) hCm hdec
    (η / 4) (by positivity)
  -- 4. the derived clean-nonzero theorem (V27)
  obtain ⟨M4, hM4⟩ := nonzero_branch_small B.di (fun M => DEnz M (LamFam E Psm Prd lev X wτ S τ M))
    (fun M => B.nonzero S τ M) (η / 4) (by positivity)
  -- 8. tensor approximation
  have hCt := B.tensor.Ct_nonneg
  set δ : ℝ := η / (4 * (Ct + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨M3, hM3⟩ := hat_approximation_eventually_small B.hat (δ ^ 2) (by positivity)
  refine ⟨S, τ, max (max M1 M2) (max M3 M4), fun M hM => ?_⟩
  have e1 := hM1 M (by omega)
  have e2 := hM2 M (by omega)
  have e4 := hM4 M (by omega)
  have e3 : Real.sqrt |EAB M| ≤ δ := by
    rw [Real.sqrt_le_left hδ.le]; exact hM3 M (by omega)
  have e3' : Ct * Real.sqrt |EAB M| ≤ η / 4 := by
    calc Ct * Real.sqrt |EAB M| ≤ Ct * δ := mul_le_mul_of_nonneg_left e3 hCt
      _ ≤ (Ct + 1) * δ := by nlinarith
      _ = η / 4 := by simp only [δ]; field_simp
  have hmain : (model S M).Mnew (pref Li phiW N M) (LamFam E Psm Prd lev X wτ S τ M) ≤
      ((A_C : ℚ) : ℝ) * (LF / I) + η / 4 := e1
  unfold BxSq
  simp only at e4
  linarith

/-- **Route-C pair baseline after the full repair** (LEAN CONDITIONAL on
`FinalAnalyticProviders`; no monolithic source-class provider is used). -/
theorem routeC_pair_baseline_after_full_repair {τC : FixedTupleC V} {W : WeightSystem τC}
    {K : ℕ} {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ} {Psm Prd : ℕ → ℝ → Finset ℕ}
    {lev X : ℝ → ℝ} {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ}
    {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ} {N Li : ℕ → ℝ} {phiW : ℝ}
    {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ} {Us Ur : ℕ → ℕ → Finset ℕ}
    {D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct Cnz err : ℝ} {muLo WHi : ℚ} {muF : ℝ}
    {DIClass : ResearchBankV27.DISpectral.KloostermanData → Prop}
    (B : FinalAnalyticProviders τC W K h F E Psm Prd lev X wτ r Sd LF I N Li phiW model Kh EAB
      Us Ur D0 D1 D2 Db DEnz Ct Cnz err muLo WHi muF DIClass)
    (G : SieveGeometry E Psm Prd h model Us Ur) (cd : RoundedCellData Prd wτ X)
    (hLi : ∀ M, 0 ≤ Li M) (hphi : 0 < phiW) (hWF : 0 ≤ LF / I) :
    RouteCBaselineProvider τC W N (LF / I) err := by
  refine ⟨fun η hη => ?_⟩
  obtain ⟨S, τ, M0, hM0⟩ := bx_norm_bound B G cd hLi hphi hWF η hη
  refine ⟨M0, fun M hM => ?_⟩
  have hdec := B.tensor.decomp S τ M
  have hb := hM0 M hM
  unfold BxSq at hb
  linarith

/-- **Final pair ratio** (LEAN CONDITIONAL): with `err = −423/5`, eventually
`P_actual / N ≤ A_C W_F + 27/5 + η`. -/
theorem pair_ratio_final {τC : FixedTupleC V} {W : WeightSystem τC}
    {K : ℕ} {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ} {Psm Prd : ℕ → ℝ → Finset ℕ}
    {lev X : ℝ → ℝ} {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ}
    {Sd : ResearchBankV23.SingularFactors.SingularData} {LF I : ℝ} {N Li : ℕ → ℝ} {phiW : ℝ}
    {model : ℕ → ℕ → PrincipalModel h} {Kh : ℕ} {EAB : ℕ → ℝ} {Us Ur : ℕ → ℕ → Finset ℕ}
    {D0 D1 D2 Db DEnz : ℕ → (Finset ℕ → ℝ) → ℝ} {Ct Cnz : ℝ} {muLo WHi : ℚ} {muF : ℝ}
    {DIClass : ResearchBankV27.DISpectral.KloostermanData → Prop}
    (B : FinalAnalyticProviders τC W K h F E Psm Prd lev X wτ r Sd LF I N Li phiW model Kh EAB
      Us Ur D0 D1 D2 Db DEnz Ct Cnz ((ExactParameterInstantiation.errFinal : ℚ) : ℝ) muLo WHi muF DIClass)
    (G : SieveGeometry E Psm Prd h model Us Ur) (cd : RoundedCellData Prd wτ X)
    (hLi : ∀ M, 0 ≤ Li M) (hphi : 0 < phiW) (hWF : 0 ≤ LF / I) :
    ∀ η > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      Pair τC W M / N M ≤ ((A_C : ℚ) : ℝ) * (LF / I) + 27 / 5 + η := by
  intro η hη
  obtain ⟨M0, hM0⟩ := (routeC_pair_baseline_after_full_repair B G cd hLi hphi hWF).eventual η hη
  refine ⟨M0, fun M hM => ?_⟩
  have := hM0 M hM
  have herr : ((ExactParameterInstantiation.errFinal : ℚ) : ℝ) = -423 / 5 := by
    unfold ExactParameterInstantiation.errFinal; push_cast; ring
  rw [herr] at this
  linarith

end FinalPairComposition
end ResearchBankV28
end Erdos287
