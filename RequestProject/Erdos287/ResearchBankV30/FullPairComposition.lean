import RequestProject.Erdos287.ResearchBankV29.ProviderElimination

/-!
# Erdős #287 — Research Bank V30 §14: full end-to-end pair composition

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

`full_pair_composition` composes, in ONE proof and by explicit declaration references:

1. completed positive upper sieve / source decomposition of the SAME weight
   `Λ = LamFam S τ M = LambdaNewPlus …` — `lamFam_source_decomposition` (V24, LEAN BANK);
2. principal + remainder split — the glue owner's `tensor.decomp` (INTERNAL, not eliminated);
3. zero / one-large / two-large / boundary branches — `derived_source_class_provider` (V28) and
   `distribution_error_small` (V24) from the four EXTERNAL branch class bounds;
4. Type-II / clean nonzero theorem — `nonzero_branch_small` (V28, from the V27 derived
   `clean_nonzero_derived`), with the glue owner's `nonzero` realizations (INTERNAL);
5. same-weight principal bound — `principal_budget_le_A_C` (V23);
6. tensor approximation (`B_x` norm) — `hat_approximation_eventually_small` (V23);
7. actual-measure transfer and the final `P_actual/N_x` bound with the exact constant
   `90 + errFinal = 27/5`.

Conclusion (explicit eventual / error interface): for every `η > 0` there are `S, τ` (chosen
BEFORE `M`) and `M₀` such that for all `M ≥ M₀`: the `B_x` norm of the weight `LamFam S τ M`
satisfies `‖B_x‖² ≤ A_C W_F + η`, and `P_actual(M)/N(M) ≤ A_C W_F + 27/5 + η`.

LEAN CONDITIONAL on `MinimalExternalAnalyticProviders`, the certificate AND the internal glue
owner `InternalGlueOwner` (which V29 could not eliminate).
-/

namespace Erdos287
namespace ResearchBankV30
namespace FullPairComposition

open Finset
open ResearchBankV22.RosserCostProvider
open ResearchBankV23.PrincipalEuler ResearchBankV23.HatApproximationProvider
open ResearchBankV23.PrincipalBudget
open ResearchBankV16.RouteCParameters ResearchBankV16.RouteCConsumer
open ResearchBankV24.RepairedProvider ResearchBankV24.RepairedRouteCBaseline
open ResearchBankV27.DISpectral
open ResearchBankV28.RepairedAnalyticBundle ResearchBankV28.ExactParameterInstantiation
open ResearchBankV28.FinalPairComposition
open ResearchBankV29.ProviderElimination ResearchBankV29.FunctionalCertificate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Full end-to-end pair composition** (LEAN CONDITIONAL). -/
theorem full_pair_composition {τC : FixedTupleC V} {W : WeightSystem τC} {K : ℕ} {h : ℕ → ℝ}
    {F : ℝ → ℝ} {E : Finset ℕ} {Psm Prd : ℕ → ℝ → Finset ℕ} {lev X : ℝ → ℝ}
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
    ∀ η > 0, ∃ S : ℕ, ∃ τ : ℝ, ∃ M₀ : ℕ, ∀ M ≥ M₀,
      BxSq model (pref Li phiW N) (LamFam E Psm Prd lev X wτ) (sumDE D0 D1 D2 Db) DEnz EAB Ct
          S τ M ≤ ((A_C : ℚ) : ℝ) * (LF / I) + η ∧
        Pair τC W M / N M ≤ ((A_C : ℚ) : ℝ) * (LF / I) + 27 / 5 + η := by
  intro η hη
  have hWF : 0 ≤ LF / I := C.WF_nonneg
  -- 5. same-weight principal bound (V23)
  obtain ⟨S, -, τ, -, M1, hM1⟩ := principal_budget_le_A_C Mn.rosser Mn.tuple Mn.euler G.hU G.d1
    G.d2 G.d3 G.hh hLi hphi hWF (η / 4) (by positivity)
  -- 1. completed positive sieve: the SAME weight has a source decomposition (V24)
  set Cm : ℝ := (((cd.R S τ + 1) ^ cd.nC S τ : ℕ) : ℝ) * 3 ^ cd.R S τ
  have hCm : 0 ≤ Cm := by positivity
  have hdec : ∀ M, SourceDecomposition (LamFam E Psm Prd lev X wτ S τ M) (Us S M) (Ur S M) Cm := by
    intro M
    rw [G.hUs, G.hUr]
    exact lamFam_source_decomposition cd G.d1 G.d2 G.d3 S τ M
  -- 3. zero / one-large / two-large / boundary branches (EXTERNAL class bounds)
  have Psrc := derived_source_class_provider Mn.zeroFreq Mn.oneLarge Mn.twoLarge Mn.boundary
  obtain ⟨M2, hM2⟩ := distribution_error_small Psrc S (LamFam E Psm Prd lev X wτ S τ) hCm hdec
    (η / 4) (by positivity)
  -- 4. Type-II / clean nonzero theorem (V27 derived, glue-owner realizations)
  obtain ⟨M4, hM4⟩ := nonzero_branch_small Mn.di
    (fun M => DEnz M (LamFam E Psm Prd lev X wτ S τ M)) (fun M => Gl.nonzero S τ M)
    (η / 4) (by positivity)
  -- 6. tensor approximation / B_x norm
  have hCt := Gl.tensor.Ct_nonneg
  set δ : ℝ := η / (4 * (Ct + 1))
  have hδ : 0 < δ := by positivity
  obtain ⟨M3, hM3⟩ := hat_approximation_eventually_small Mn.hat (δ ^ 2) (by positivity)
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
  -- 2./7. principal + remainder split and actual-measure transfer (glue owner)
  have hsplit := Gl.tensor.decomp S τ M
  have herr : ((errFinal : ℚ) : ℝ) = -423 / 5 := by unfold errFinal; push_cast; ring
  have hmain : (model S M).Mnew (pref Li phiW N M) (LamFam E Psm Prd lev X wτ S τ M) ≤
      ((A_C : ℚ) : ℝ) * (LF / I) + η / 4 := e1
  simp only at e4
  rw [herr] at hsplit
  unfold BxSq
  constructor <;> linarith

end FullPairComposition
end ResearchBankV30
end Erdos287
