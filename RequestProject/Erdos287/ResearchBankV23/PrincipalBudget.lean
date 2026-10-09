import RequestProject.Erdos287.ResearchBankV23.PrincipalEulerProvider
import RequestProject.Erdos287.ResearchBankV22.IndependentFactorization
import RequestProject.Erdos287.ResearchBankV22.RosserCostProvider
import RequestProject.Erdos287.ResearchBankV16.RouteCParameters

/-!
# Erdős #287 — Research Bank V23 §8: the principal budget

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## Exact rational arithmetic (LEAN BANK)

With `vartheta = 273/500`, `rho = 1/1000000`, `vartheta0 = 545999/1000000`, `b_z = 501/1000`,
`A_C = 1000273/273000` (the frozen V16 value):

* **`two_div_diff`** — `2/vartheta0 - 2/vartheta = 1000/149057727`;
* **`principal_slack`** — `A_C - 2/vartheta0 - 1/5000 = 147807727/186322158750 > 0`;
* `s0_mul_b_z` — `s0 · b_z = vartheta0`.

## Exact cost algebra for the completed weight (LEAN BANK)

* `costU_muE` — the exceptional presieve has normalized cost exactly `1`
  (`C_{μ_E}(q) = 1` whenever `q_p ≠ 1` on `E`); `P_E` is kept, it merely costs `1`;
* **`cost_LambdaNewPlus_eq`** — `C_{Λ_new^+}(h) = C_{β_sm^+ ⋆ ℓ_rd}(h)`.

## Conditional budget (LEAN CONDITIONAL on `RosserScalarProvider`,
## `PrimeHarmonicTupleProvider`, `PrincipalEulerProvider`)

* **`principal_budget_conditional`** — for every `ε > 0` there are `S`, then `τ`, then `M₀`
  (order `S → τ → x`) with

      M_new(S, τ, M) ≤ (2/vartheta0 + 1/5000) W_F + ε      for all M ≥ M₀,

  where `M_new` is the V23 principal functional of the SAME weight `Λ_new^+` and `W_F = L_ij(F)/I`;
* `principal_budget_conditional_mul` — the multiplicative form `≤ (2/vartheta0 + 1/5000 + ε) W_F`
  when `W_F > 0`;
* **`principal_budget_le_A_C`** — hence `M_new ≤ A_C W_F + ε` eventually.
-/

namespace Erdos287
namespace ResearchBankV23
namespace PrincipalBudget

open Finset
open ResearchBankV22.PositiveSieveParameters ResearchBankV22.RoundedRoughSieve
open ResearchBankV22.CompletedPositiveWeight ResearchBankV22.RosserCostProvider
open ResearchBankV22.IndependentFactorization ResearchBankV22.SmallPrimeUpperSieve
open PrincipalEuler

/-! ### Exact rational arithmetic -/

/-- **`2/vartheta0 - 2/vartheta = 1000/149057727`.** -/
theorem two_div_diff : 2 / vartheta0 - 2 / vartheta = 1000 / 149057727 := by
  norm_num [vartheta0, vartheta, rho]

/-- **Principal slack** `A_C - 2/vartheta0 - 1/5000 = 147807727/186322158750 > 0`. -/
theorem principal_slack :
    ResearchBankV16.RouteCParameters.A_C - 2 / vartheta0 - 1 / 5000 =
        147807727 / 186322158750 ∧
      (0 : ℚ) < 147807727 / 186322158750 := by
  refine ⟨?_, by norm_num⟩
  norm_num [ResearchBankV16.RouteCParameters.A_C, vartheta0, vartheta, rho]

theorem s0_mul_b_z : s0 * b_z = vartheta0 := by norm_num [s0, vartheta0, vartheta, rho, b_z]

theorem budget_lt_A_C :
    ((2 / vartheta0 + 1 / 5000 : ℚ) : ℝ) < ((ResearchBankV16.RouteCParameters.A_C : ℚ) : ℝ) := by
  have := principal_slack.1
  have h2 : (2 / vartheta0 + 1 / 5000 : ℚ) < ResearchBankV16.RouteCParameters.A_C := by
    linarith [principal_slack.2]
  exact_mod_cast h2

/-! ### Exact cost algebra -/

section CostAlgebra

variable {γ : Type*} [DecidableEq γ]

/-- **The exceptional presieve costs exactly `1`.** -/
theorem costU_muE (E : Finset γ) (q : γ → ℝ) (hq : ∀ p ∈ E, q p ≠ 1) :
    costU E (muE E) q = 1 := by
  unfold costU numerU denomU
  have hden : ∏ p ∈ E, (1 - q p) ≠ 0 :=
    prod_ne_zero_iff.2 fun p hp => sub_ne_zero.2 (Ne.symm (hq p hp))
  rw [div_eq_one_iff_eq hden]
  have h1 : ∏ p ∈ E, (1 - q p) = ∏ p ∈ E, ((-q p) + 1) := prod_congr rfl fun p _ => by ring
  rw [h1, prod_add]
  refine sum_congr rfl fun A hA => ?_
  rw [mem_powerset] at hA
  simp only [muE, if_pos hA, prod_const_one, mul_one, prod_neg]

/-- **`C_{Λ_new^+}(h) = C_{β_sm^+ ⋆ ℓ_rd}(h)`** (disjoint universes, `h ≠ 1` on `E`). -/
theorem cost_LambdaNewPlus_eq {E Psm Prd : Finset ℕ} {level X : ℝ} {w : ℕ → ℝ}
    (h1 : Disjoint E Psm) (h2 : Disjoint E Prd) (h3 : Disjoint Psm Prd) (h : ℕ → ℝ)
    (hE : ∀ p ∈ E, h p ≠ 1) :
    costU (E ∪ Psm ∪ Prd) (LambdaNewPlus E Psm Prd level w X) h =
      costU (Psm ∪ Prd) (conv (rosserBeta Psm level) (ellRd Prd w X)) h := by
  unfold LambdaNewPlus completedWeight rosserBeta
  rw [← conv_assoc_disjoint (muE_supported E) (ellRd_supported _ _ _) (ellRd_supported _ _ _)
    h1 h2 h3, union_assoc,
    costU_conv (muE_supported E) (conv_supported (ellRd_supported _ _ _) (ellRd_supported _ _ _))
      (disjoint_union_right.2 ⟨h1, h2⟩), costU_muE E h hE, one_mul]

end CostAlgebra

/-! ### The conditional principal budget -/

/-- `F(s0) · e^{-γ}/b_z = 2/vartheta0`. -/
theorem F0_mul_g {F : ℝ → ℝ}
    (hF : F (s0 : ℝ) = 2 * Real.exp Real.eulerMascheroniConstant / (s0 : ℝ)) :
    F (s0 : ℝ) * gConst = ((2 / vartheta0 : ℚ) : ℝ) := by
  rw [hF]
  unfold gConst
  have hs : (s0 : ℝ) * (b_z : ℝ) = (vartheta0 : ℝ) := by exact_mod_cast s0_mul_b_z
  have hs0 : (s0 : ℝ) ≠ 0 := by
    have := one_lt_s0.1; have : (0 : ℝ) < s0 := by exact_mod_cast lt_trans one_pos this
    exact this.ne'
  have hb : (b_z : ℝ) ≠ 0 := by norm_num [b_z]
  have he : Real.exp Real.eulerMascheroniConstant * Real.exp (-Real.eulerMascheroniConstant) = 1 :=
    by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  push_cast
  rw [← hs]
  field_simp
  linear_combination he

variable {K : ℕ} {h : ℕ → ℝ} {F : ℝ → ℝ} {E : Finset ℕ} {Psm Prd : ℕ → ℝ → Finset ℕ}
  {lev X : ℝ → ℝ} {wτ : ℝ → ℝ → ℕ → ℝ} {r : ℕ} {Sd : SingularFactors.SingularData} {LF I : ℝ}
  {S0 N Li : ℕ → ℝ} {phiW : ℝ} {model : ℕ → ℕ → PrincipalModel h}

/-- **The conditional principal budget** (LEAN CONDITIONAL).  In the order `S → τ → x`: -/
theorem principal_budget_conditional
    (hR : RosserScalarProvider K h F Psm Prd lev X) (hT : PrimeHarmonicTupleProvider h Prd X wτ)
    (P : PrincipalEulerProvider h r Sd LF I S0 N Li phiW model)
    (hU : ∀ S M, (model S M).U = E ∪ Psm S M ∪ Prd S M)
    (h1 : ∀ S x, Disjoint E (Psm S x)) (h2 : ∀ S x, Disjoint E (Prd S x))
    (h3 : ∀ S x, Disjoint (Psm S x) (Prd S x))
    (hh : ∀ S x, ∀ p ∈ E ∪ Psm S x ∪ Prd S x, h p < 1)
    (hLi : ∀ M, 0 ≤ Li M) (hphi : 0 < phiW) (hWF : 0 ≤ LF / I) :
    ∀ ε > 0, ∃ S : ℕ, 0 < S ∧ ∃ τ : ℝ, 0 < τ ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀,
      (model S M).Mnew (pref Li phiW N M)
          (LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M)) ≤
        ((2 / vartheta0 + 1 / 5000 : ℚ) : ℝ) * (LF / I) + ε := by
  intro ε hε
  set WF := LF / I
  set F0 := F (s0 : ℝ)
  have hF0 : F0 = 2 * Real.exp Real.eulerMascheroniConstant / (s0 : ℝ) :=
    hR.F_rosser _ (by exact_mod_cast (one_lt_s0).1.le) (by exact_mod_cast (one_lt_s0).2.le)
  have hs0 : (0 : ℝ) < (s0 : ℝ) := by exact_mod_cast lt_trans one_pos one_lt_s0.1
  have hF0pos : 0 < F0 := by rw [hF0]; exact div_pos (by positivity) hs0
  obtain ⟨hg0, hg2⟩ := gConst_pos_le_two
  have hFg := F0_mul_g hF0
  set ε1 := min (1 / 2) (ε / (4 * (WF + 1))) with hε1
  have hε1pos : 0 < ε1 := lt_min (by norm_num) (by positivity)
  have hε1a : ε1 ≤ 1 / 2 := min_le_left _ _
  have hε1b : ε1 ≤ ε / (4 * (WF + 1)) := min_le_right _ _
  obtain ⟨ε2, hε2⟩ : ∃ e : ℝ, e = ε / (2 * (F0 + 2)) := ⟨_, rfl⟩
  have hε2pos : 0 < ε2 := by rw [hε2]; positivity
  obtain ⟨S, hS, τ, hτ, x0, hx0⟩ := completed_cost_bound hR hT h3 ε1 hε1pos
  refine ⟨S, hS, τ, hτ, ?_⟩
  obtain ⟨M1, hM1⟩ := P.sifted_main S ε2 hε2pos
  obtain ⟨M2, hM2⟩ := P.normalization_agreement 1 one_pos
  refine ⟨max (max M1 M2) ⌈x0⌉₊, fun M hM => ?_⟩
  have hMa : M1 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMb : M2 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hceil : ⌈x0⌉₊ ≤ M := le_trans (le_max_right _ _) hM
  have hMc : x0 ≤ (M : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hceil)
  have hN := (hM2 M hMb).1
  have hpref : 0 ≤ pref Li phiW N M := by
    unfold pref; exact div_nonneg (hLi M) (mul_pos hphi hN).le
  -- the same-weight bound
  set m := model S M
  have hmain : m.Mnew (pref Li phiW N M)
      (LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M)) ≤
      costU m.U (LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M)) h *
        m.sifted (pref Li phiW N M) :=
    SameWeightPrincipal.same_weight_principal_bound hpref
      (LambdaNewPlus_nonneg (h1 S M) (h2 S M) (h3 S M)) m.μ_nonneg m.q_nonneg m.q_le_h
      (fun p hp => hh S M p (by rw [← hU S M]; exact hp)) m.B
  rw [hU S M, cost_LambdaNewPlus_eq (h1 S M) (h2 S M) (h3 S M) h
    (fun p hp => (hh S M p (mem_union_left _ (mem_union_left _ hp))).ne)] at hmain
  set c := costU (Psm S M ∪ Prd S M) (conv (rosserBeta (Psm S M) (lev M))
    (ellRd (Prd S M) (wτ τ M) (X M))) h
  have hc : c ≤ F0 + 1 / 10000 + ε1 := hx0 M hMc
  set sft := m.sifted (pref Li phiW N M)
  have hsft0 : 0 ≤ sft := m.sifted_nonneg hpref
  have hsft : sft ≤ gConst * WF + ε2 := by
    have := hM1 M hMa
    rw [SingularFactors.singular_cancellation, div_self P.Sall_ne, one_mul] at this
    linarith [(abs_le.1 this).2]
  have htarget0 : 0 ≤ ((2 / vartheta0 + 1 / 5000 : ℚ) : ℝ) * WF := by
    apply mul_nonneg _ hWF; norm_num [vartheta0, vartheta, rho]
  by_cases hc0 : c ≤ 0
  · have : c * sft ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 hsft0
    linarith
  push_neg at hc0
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = F0 + 1 / 10000 + ε1 := ⟨_, rfl⟩
  rw [← hAdef] at hc
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hstep1 : c * sft ≤ A * sft := mul_le_mul_of_nonneg_right hc hsft0
  have hstep2 : A * sft ≤ A * (gConst * WF + ε2) := mul_le_mul_of_nonneg_left hsft hA0
  have hexp : A * (gConst * WF + ε2) =
      F0 * gConst * WF + gConst / 10000 * WF + ε1 * gConst * WF + A * ε2 := by rw [hAdef]; ring
  have hq : ((2 / vartheta0 + 1 / 5000 : ℚ) : ℝ) * WF =
      ((2 / vartheta0 : ℚ) : ℝ) * WF + 1 / 5000 * WF := by push_cast; ring
  have ha : gConst / 10000 * WF ≤ 1 / 5000 * WF := by
    apply mul_le_mul_of_nonneg_right _ hWF; linarith
  have hb : ε1 * gConst * WF ≤ ε / 2 := by
    have e1 : ε1 * gConst * WF ≤ ε1 * 2 * (WF + 1) := by
      have : gConst * WF ≤ 2 * (WF + 1) := by nlinarith
      nlinarith
    have e2 : ε1 * 2 * (WF + 1) ≤ ε / (4 * (WF + 1)) * 2 * (WF + 1) := by
      have : 0 ≤ 2 * (WF + 1) := by linarith
      nlinarith
    have e3 : ε / (4 * (WF + 1)) * 2 * (WF + 1) = ε / 2 := by field_simp; ring
    linarith
  have hcA : A * ε2 ≤ ε / 2 := by
    have hA2 : A ≤ F0 + 2 := by rw [hAdef]; linarith
    have e : (F0 + 2) * ε2 = ε / 2 := by
      rw [hε2]; field_simp
    have := mul_le_mul_of_nonneg_right hA2 hε2pos.le
    linarith
  calc m.Mnew (pref Li phiW N M) _ ≤ c * sft := hmain
    _ ≤ A * (gConst * WF + ε2) := le_trans hstep1 hstep2
    _ ≤ _ := by rw [hexp, hq, hFg]; linarith

/-- **Multiplicative form** `M_new ≤ (2/vartheta0 + 1/5000 + ε) W_F` when `W_F > 0`. -/
theorem principal_budget_conditional_mul
    (hR : RosserScalarProvider K h F Psm Prd lev X) (hT : PrimeHarmonicTupleProvider h Prd X wτ)
    (P : PrincipalEulerProvider h r Sd LF I S0 N Li phiW model)
    (hU : ∀ S M, (model S M).U = E ∪ Psm S M ∪ Prd S M)
    (h1 : ∀ S x, Disjoint E (Psm S x)) (h2 : ∀ S x, Disjoint E (Prd S x))
    (h3 : ∀ S x, Disjoint (Psm S x) (Prd S x))
    (hh : ∀ S x, ∀ p ∈ E ∪ Psm S x ∪ Prd S x, h p < 1)
    (hLi : ∀ M, 0 ≤ Li M) (hphi : 0 < phiW) (hWF : 0 < LF / I) :
    ∀ ε > 0, ∃ S : ℕ, 0 < S ∧ ∃ τ : ℝ, 0 < τ ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀,
      (model S M).Mnew (pref Li phiW N M)
          (LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M)) ≤
        (((2 / vartheta0 + 1 / 5000 : ℚ) : ℝ) + ε) * (LF / I) := by
  intro ε hε
  obtain ⟨S, hS, τ, hτ, M₀, hM⟩ := principal_budget_conditional hR hT P hU h1 h2 h3 hh hLi hphi
    hWF.le (ε * (LF / I)) (mul_pos hε hWF)
  exact ⟨S, hS, τ, hτ, M₀, fun M hM' => by have := hM M hM'; linarith⟩

/-- **`M_new ≤ A_C W_F + ε` eventually** (LEAN CONDITIONAL). -/
theorem principal_budget_le_A_C
    (hR : RosserScalarProvider K h F Psm Prd lev X) (hT : PrimeHarmonicTupleProvider h Prd X wτ)
    (P : PrincipalEulerProvider h r Sd LF I S0 N Li phiW model)
    (hU : ∀ S M, (model S M).U = E ∪ Psm S M ∪ Prd S M)
    (h1 : ∀ S x, Disjoint E (Psm S x)) (h2 : ∀ S x, Disjoint E (Prd S x))
    (h3 : ∀ S x, Disjoint (Psm S x) (Prd S x))
    (hh : ∀ S x, ∀ p ∈ E ∪ Psm S x ∪ Prd S x, h p < 1)
    (hLi : ∀ M, 0 ≤ Li M) (hphi : 0 < phiW) (hWF : 0 ≤ LF / I) :
    ∀ ε > 0, ∃ S : ℕ, 0 < S ∧ ∃ τ : ℝ, 0 < τ ∧ ∃ M₀ : ℕ, ∀ M ≥ M₀,
      (model S M).Mnew (pref Li phiW N M)
          (LambdaNewPlus E (Psm S M) (Prd S M) (lev M) (wτ τ M) (X M)) ≤
        ((ResearchBankV16.RouteCParameters.A_C : ℚ) : ℝ) * (LF / I) + ε := by
  intro ε hε
  obtain ⟨S, hS, τ, hτ, M₀, hM⟩ :=
    principal_budget_conditional hR hT P hU h1 h2 h3 hh hLi hphi hWF ε hε
  refine ⟨S, hS, τ, hτ, M₀, fun M hM' => le_trans (hM M hM') ?_⟩
  have := mul_le_mul_of_nonneg_right budget_lt_A_C.le hWF
  linarith

end PrincipalBudget
end ResearchBankV23
end Erdos287
