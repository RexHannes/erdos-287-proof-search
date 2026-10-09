import RequestProject.Erdos287.ResearchBankV22.CellColouring
import RequestProject.Erdos287.ResearchBankV22.PositiveSieveParameters
import RequestProject.Erdos287.ResearchBankV21.NormalizedSieveMonotonicity
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Erdős #287 — Research Bank V22 §10: Rosser cost as an explicit provider

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

## Finite part (LEAN BANK)

* `costU U w q = (Σ_{A ⊆ U} w(A) ∏_{p∈A} q_p) / ∏_{p∈U} (1 - q_p)` — the normalized sieve cost
  of an atom-set weight on a finite prime universe `U`;
* `costU_eq_normCost` — it IS the V21 functional `C_λ(q)` of the pulled-back weight (bridge);
* **`costU_mono`** — V21 monotonicity for the actual weights: if the divisor sums are `≥ 0`
  (e.g. `ℓ_rd`, `β_sm^+`, `Λ_new^+`) then `q ≤ h < 1` implies `cost(q) ≤ cost(h)`;
* **`costU_conv`** — costs multiply over disjoint prime universes:
  `C_{f⋆g}(q) = C_f(q) · C_g(q)`;
* `thinLayer_length_le_R` — a thin-layer tuple with all `t_i ≥ nu` and total `≤ vartheta0` has
  at most `R = ⌊vartheta0/nu⌋` atoms;
* `CnuR S` — the explicit finite rounding constant
  `C_{nu,R} = vartheta0/3 · Σ_{k=1}^{R} ⌈k/2⌉ nu^{-k} (b_z - nu)^{k-1}`, `CnuR_pos`.

## Analytic part (EXTERNAL PROVIDER interfaces, never constructed)

* `DimensionOneDensity h K` — `h(p) = 1/p + O_K(1/p²)` and the two-sided Mertens condition;
* `RosserScalarProvider` — the ordinary dimension-one Rosser asymptotic, in ε/eventual form:
  small-prime cost `≤ F(S) + ε`, unrounded rough cost `≤ F(s0) + ε`, `F(s) = 2e^γ/s` on
  `[1,3]`, `F(S) → 1`;
* `PrimeHarmonicTupleProvider` — rounding error `≤ C_{nu,R} τ + ε` (thin-layer prime harmonic
  tuple estimate).

## Conditional consequence (LEAN CONDITIONAL)

* **`completed_cost_bound`** — in the quantifier order `S → τ → x`:
  `C_{β_sm^+ ⋆ ℓ_rd}(h) ≤ F(s0) + 1/10000 + ε` eventually, for every `ε > 0`
  (the `o(1)` is represented by the explicit `ε`/eventual quantifiers).
-/

namespace Erdos287
namespace ResearchBankV22
namespace RosserCostProvider

open Finset RoundedRoughSieve CompletedPositiveWeight CellColouring PositiveSieveParameters
open ResearchBankV21.FiniteSieveSetup ResearchBankV21.NormalizedSieveMonotonicity

section Cost

variable {γ : Type*} [DecidableEq γ]

/-- Numerator `Σ_{A ⊆ U} w(A) ∏_{p∈A} q_p`. -/
def numerU (U : Finset γ) (w : Finset γ → ℝ) (q : γ → ℝ) : ℝ :=
  ∑ A ∈ U.powerset, w A * ∏ p ∈ A, q p

/-- Denominator `∏_{p∈U} (1 - q_p)`. -/
def denomU (U : Finset γ) (q : γ → ℝ) : ℝ := ∏ p ∈ U, (1 - q p)

/-- **Normalized sieve cost on the universe `U`.** -/
noncomputable def costU (U : Finset γ) (w : Finset γ → ℝ) (q : γ → ℝ) : ℝ :=
  numerU U w q / denomU U q

/-- Pull-back of an atom-set weight to the finite type `U`. -/
def pull (U : Finset γ) (w : Finset γ → ℝ) : Finset U → ℝ :=
  fun A => w (A.map (Function.Embedding.subtype (· ∈ U)))

theorem sum_univ_pull (U : Finset γ) (F : Finset γ → ℝ) :
    ∑ A : Finset U, F (A.map (Function.Embedding.subtype (· ∈ U))) = ∑ B ∈ U.powerset, F B := by
  refine sum_nbij' (fun A => A.map (Function.Embedding.subtype (· ∈ U)))
    (fun B => B.subtype (· ∈ U)) ?_ ?_ ?_ ?_ ?_
  · intro A _
    rw [mem_powerset]
    intro x hx
    obtain ⟨y, -, rfl⟩ := mem_map.1 hx
    exact y.2
  · intro _ _; exact mem_univ _
  · intro A _
    ext x; simp
  · intro B hB
    exact subtype_map_of_mem fun x hx => mem_powerset.1 hB hx
  · intro _ _; rfl

theorem divSum_pull (U : Finset γ) (w : Finset γ → ℝ) (S : Finset U) :
    divSum (pull U w) S = dsum w (S.map (Function.Embedding.subtype (· ∈ U))) := by
  unfold divSum dsum pull
  refine sum_nbij' (fun A => A.map (Function.Embedding.subtype (· ∈ U)))
    (fun B => B.subtype (· ∈ U)) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    rw [mem_powerset] at hA ⊢
    exact map_subset_map.2 hA
  · intro B hB
    rw [mem_powerset] at hB ⊢
    intro x hx
    rw [mem_subtype] at hx
    obtain ⟨y, hy, hyx⟩ := mem_map.1 (hB hx)
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  · intro A _
    ext x; simp
  · intro B hB
    rw [mem_powerset] at hB
    refine subtype_map_of_mem fun x hx => ?_
    obtain ⟨y, -, rfl⟩ := mem_map.1 (hB hx)
    exact y.2
  · intro _ _; rfl

/-- **Bridge**: `costU` is the V21 normalized functional of the pulled-back weight. -/
theorem costU_eq_normCost (U : Finset γ) (w : Finset γ → ℝ) (q : γ → ℝ) :
    costU U w q = normCost (pull U w) (fun p : U => q p) := by
  unfold costU normCost numerU numer denomU denom pull
  congr 1
  · rw [← sum_univ_pull U (fun B => w B * ∏ p ∈ B, q p)]
    refine sum_congr rfl fun A _ => ?_
    rw [prod_map]; rfl
  · rw [← prod_coe_sort]

/-- **V21 monotonicity for actual weights**: nonnegative divisor sums + `q ≤ h < 1`. -/
theorem costU_mono {U : Finset γ} {w : Finset γ → ℝ} (hw : ∀ D, 0 ≤ dsum w D) {q h : γ → ℝ}
    (hq0 : ∀ p ∈ U, 0 ≤ q p) (hqh : ∀ p ∈ U, q p ≤ h p) (hh : ∀ p ∈ U, h p < 1) :
    costU U w q ≤ costU U w h := by
  rw [costU_eq_normCost, costU_eq_normCost]
  exact normCost_mono _ (fun S => by rw [divSum_pull]; exact hw _)
    (fun p => hq0 p p.2) (fun p => hqh p p.2) (fun p => hh p p.2)

/-- **Costs multiply over disjoint prime universes.** -/
theorem costU_conv {f g : Finset γ → ℝ} {U1 U2 : Finset γ} (hf : SupportedIn f U1)
    (hg : SupportedIn g U2) (hd : Disjoint U1 U2) (q : γ → ℝ) :
    costU (U1 ∪ U2) (conv f g) q = costU U1 f q * costU U2 g q := by
  unfold costU
  rw [div_mul_div_comm]
  congr 1
  · unfold numerU
    rw [sum_mul_sum, ← sum_product']
    refine sum_nbij' (fun A => (A ∩ U1, A ∩ U2)) (fun BC => BC.1 ∪ BC.2) ?_ ?_ ?_ ?_ ?_
    · intro A _
      simp only [mem_product, mem_powerset]
      exact ⟨inter_subset_right, inter_subset_right⟩
    · intro BC hBC
      simp only [mem_product, mem_powerset] at hBC
      rw [mem_powerset]
      exact union_subset_union hBC.1 hBC.2
    · intro A hA
      rw [mem_powerset] at hA
      simp only
      rw [← inter_union_distrib_left, inter_eq_left.2 hA]
    · intro BC hBC
      simp only [mem_product, mem_powerset] at hBC
      obtain ⟨B, C⟩ := BC
      simp only at hBC ⊢
      have h1 : (B ∪ C) ∩ U1 = B := by
        rw [union_inter_distrib_right, inter_eq_left.2 hBC.1,
          disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left hBC.2 hd.symm), union_empty]
      have h2 : (B ∪ C) ∩ U2 = C := by
        rw [union_inter_distrib_right, inter_eq_left.2 hBC.2,
          disjoint_iff_inter_eq_empty.1 (disjoint_of_subset_left hBC.1 hd), empty_union]
      rw [h1, h2]
    · intro A hA
      rw [mem_powerset] at hA
      simp only
      rw [conv_collapse hf hg hd, if_pos hA]
      have hdis : Disjoint (A ∩ U1) (A ∩ U2) :=
        disjoint_of_subset_left inter_subset_right (disjoint_of_subset_right inter_subset_right hd)
      have hAu : A = (A ∩ U1) ∪ (A ∩ U2) := by
        rw [← inter_union_distrib_left, inter_eq_left.2 hA]
      conv_lhs => rw [hAu, prod_union hdis]
      rw [← hAu]
      ring
  · unfold denomU
    rw [prod_union hd]

end Cost

/-! ### Thin layers and the explicit rounding constant -/

/-- The thin-layer condition for an ordered tuple `t₁ ≥ t₂ ≥ ⋯` of log-sizes (at index `j`):
`vartheta0/(1+τ) < t₁+⋯+t_{j-1} + 3 t_j ≤ vartheta0`, all `t_i ∈ [nu, b_z]`. -/
def ThinLayer (S : ℕ) (τ : ℚ) (t : List ℚ) (j : ℕ) : Prop :=
  (∀ x ∈ t, nu S ≤ x ∧ x ≤ b_z) ∧
    vartheta0 / (1 + τ) < (t.take j).sum + 3 * (t.getD j 0) ∧
    (t.take j).sum + 3 * (t.getD j 0) ≤ vartheta0

/-- **Atom count**: all `t_i ≥ nu` and total `≤ vartheta0` force at most `R` atoms. -/
theorem thinLayer_length_le_R {S : ℕ} (hS : 0 < S) (t : List ℚ) (hlow : ∀ x ∈ t, nu S ≤ x)
    (htot : t.sum ≤ vartheta0) : t.length ≤ R S := by
  have hn := nu_pos hS
  have h1 : (t.length : ℚ) * nu S ≤ t.sum := by
    have := List.card_nsmul_le_sum t (nu S) hlow
    simpa [nsmul_eq_mul] using this
  have h2 : (t.length : ℚ) ≤ vartheta0 / nu S := by
    rw [le_div_iff₀ hn]; linarith
  unfold R
  exact Nat.le_floor h2

/-- The explicit rounding constant
`C_{nu,R} = vartheta0/3 · Σ_{k=1}^{R} ⌈k/2⌉ nu^{-k} (b_z - nu)^{k-1}`. -/
def CnuR (S : ℕ) : ℚ :=
  vartheta0 / 3 * ∑ k ∈ Finset.Icc 1 (R S),
    (((k + 1) / 2 : ℕ) : ℚ) * (nu S)⁻¹ ^ k * (b_z - nu S) ^ (k - 1)

theorem CnuR_nonneg {S : ℕ} (hS : 0 < S) : 0 ≤ CnuR S := by
  unfold CnuR
  have hn := nu_pos hS
  have hb := nu_le_b_z hS
  refine mul_nonneg (by rw [vartheta0_eq]; norm_num) (sum_nonneg fun k _ => ?_)
  have : 0 ≤ b_z - nu S := by linarith
  positivity

/-! ### Analytic providers (interfaces only) -/

/-- Dimension-one density hypotheses on `h` (outside the exceptional range `p ≤ 2K+2`). -/
structure DimensionOneDensity (h : ℕ → ℝ) (K : ℕ) : Prop where
  range : ∀ p, p.Prime → 2 * K + 2 < p → 0 ≤ h p ∧ h p < 1
  near_one_over_p : ∃ C : ℝ, ∀ p, p.Prime → 2 * K + 2 < p → |h p - 1 / p| ≤ C / (p : ℝ) ^ 2
  mertens_two_sided : ∃ L : ℝ, ∀ w z : ℕ, 2 ≤ w → w ≤ z →
    |(∏ p ∈ (Finset.Ico w z).filter Nat.Prime, (1 - h p)⁻¹) - Real.log z / Real.log w| ≤
      L / Real.log w * (Real.log z / Real.log w)

/-- **Rosser scalar provider** (EXTERNAL PROVIDER): the ordinary dimension-one Rosser
asymptotic for the ACTUAL weights, in ε/eventual form.  `Psm S x`, `Prd S x` are the small and
rough prime universes, `lev x = x^rho`, `X x = x^{vartheta0}`. -/
structure RosserScalarProvider (K : ℕ) (h : ℕ → ℝ) (F : ℝ → ℝ)
    (Psm Prd : ℕ → ℝ → Finset ℕ) (lev X : ℝ → ℝ) : Prop where
  density : DimensionOneDensity h K
  F_rosser : ∀ s : ℝ, 1 ≤ s → s ≤ 3 → F s = 2 * Real.exp Real.eulerMascheroniConstant / s
  F_tendsto_one : Filter.Tendsto (fun S : ℕ => F S) Filter.atTop (nhds 1)
  small : ∀ S : ℕ, 0 < S → ∀ ε > 0, ∃ x₀ : ℝ, ∀ x ≥ x₀,
    costU (Psm S x) (ellRd (Psm S x) (fun p => (p : ℝ)) (lev x)) h ≤ F S + ε
  rough_unrounded : ∀ S : ℕ, 0 < S → ∀ ε > 0, ∃ x₀ : ℝ, ∀ x ≥ x₀,
    costU (Prd S x) (ellRd (Prd S x) (fun p => (p : ℝ)) (X x)) h ≤ F (s0 : ℝ) + ε
  small_nonneg : ∀ S x, 0 ≤ costU (Psm S x) (ellRd (Psm S x) (fun p => (p : ℝ)) (lev x)) h

/-- **Prime harmonic tuple provider** (EXTERNAL PROVIDER): the rounding error of the cell
endpoints `w_τ` is at most `C_{nu,R} τ + ε` eventually. -/
structure PrimeHarmonicTupleProvider (h : ℕ → ℝ) (Prd : ℕ → ℝ → Finset ℕ) (X : ℝ → ℝ)
    (wτ : ℝ → ℝ → ℕ → ℝ) : Prop where
  rounding : ∀ S : ℕ, 0 < S → ∀ τ > 0, ∀ ε > 0, ∃ x₀ : ℝ, ∀ x ≥ x₀,
    costU (Prd S x) (ellRd (Prd S x) (wτ τ x) (X x)) h ≤
      costU (Prd S x) (ellRd (Prd S x) (fun p => (p : ℝ)) (X x)) h + (CnuR S : ℝ) * τ + ε

/-- **Conditional completed-cost bound** in the order `S → τ → x`:
`C_{β_sm^+ ⋆ ℓ_rd}(h) ≤ F(s0) + 1/10000 + ε` eventually, for every `ε > 0`. -/
theorem completed_cost_bound {K : ℕ} {h : ℕ → ℝ} {F : ℝ → ℝ} {Psm Prd : ℕ → ℝ → Finset ℕ}
    {lev X : ℝ → ℝ} {wτ : ℝ → ℝ → ℕ → ℝ}
    (hR : RosserScalarProvider K h F Psm Prd lev X) (hT : PrimeHarmonicTupleProvider h Prd X wτ)
    (hdisj : ∀ S x, Disjoint (Psm S x) (Prd S x)) :
    QuantifierOrder (fun S τ x => costU (Psm S x ∪ Prd S x)
      (conv (ellRd (Psm S x) (fun p => (p : ℝ)) (lev x)) (ellRd (Prd S x) (wτ τ x) (X x))) h)
      (F (s0 : ℝ) + 1 / 10000) := by
  intro ε hε
  set F0 := F (s0 : ℝ)
  have hF0 : F0 = 2 * Real.exp Real.eulerMascheroniConstant / (s0 : ℝ) :=
    hR.F_rosser _ (by exact_mod_cast (one_lt_s0).1.le) (by exact_mod_cast (one_lt_s0).2.le)
  have hs0 : (0 : ℝ) < (s0 : ℝ) := by exact_mod_cast lt_trans one_pos one_lt_s0.1
  have hF0pos : 0 < F0 := by
    rw [hF0]; exact div_pos (by positivity) hs0
  -- δ-budget
  set M := F0 + 1 / 10000 + 1 with hM
  have hMpos : 0 < M := by linarith
  set δ := min (ε / (4 * M)) (1 / 40000) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ ε / (4 * M) := min_le_left _ _
  have hδ2 : δ ≤ 1 / 40000 := min_le_right _ _
  -- choose S with F(S) ≤ 1 + δ
  obtain ⟨S0, hS0⟩ := (Metric.tendsto_atTop.1 hR.F_tendsto_one) δ hδpos
  set S := max S0 1
  have hSpos : 0 < S := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hFS : F S ≤ 1 + δ := by
    have := hS0 S (le_max_left _ _)
    rw [Real.dist_eq] at this
    linarith [(abs_lt.1 this).2]
  -- choose τ with C_{nu,R} τ ≤ 1/20000
  set τ : ℝ := 1 / (20000 * ((CnuR S : ℝ) + 1))
  have hC := CnuR_nonneg hSpos
  have hCr : (0 : ℝ) ≤ (CnuR S : ℝ) := by exact_mod_cast hC
  have hτpos : 0 < τ := by positivity
  have hCτ : (CnuR S : ℝ) * τ ≤ 1 / 20000 := by
    have : (CnuR S : ℝ) * τ = (CnuR S : ℝ) / (20000 * ((CnuR S : ℝ) + 1)) := by ring
    rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨S, hSpos, τ, hτpos, ?_⟩
  -- eventual bounds
  obtain ⟨x1, h1⟩ := hR.small S hSpos δ hδpos
  obtain ⟨x2, h2⟩ := hR.rough_unrounded S hSpos δ hδpos
  obtain ⟨x3, h3⟩ := hT.rounding S hSpos τ hτpos δ hδpos
  refine ⟨max x1 (max x2 x3), fun x hx => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  show costU _ _ _ ≤ _
  rw [costU_conv (ellRd_supported _ _ _) (ellRd_supported _ _ _) (hdisj S x)]
  set a := costU (Psm S x) (ellRd (Psm S x) (fun p => (p : ℝ)) (lev x)) h
  set b := costU (Prd S x) (ellRd (Prd S x) (wτ τ x) (X x)) h
  have ha : a ≤ 1 + 2 * δ := by linarith [h1 x hx1]
  have ha0 : 0 ≤ a := hR.small_nonneg S x
  have hb : b ≤ F0 + 1 / 10000 := by linarith [h2 x hx2, h3 x hx3]
  have hbM : b ≤ M := by linarith
  have hδM : 2 * δ * M ≤ ε / 2 := by
    have := mul_le_mul_of_nonneg_right hδ1 hMpos.le
    have e : ε / (4 * M) * M = ε / 4 := by field_simp
    rw [e] at this
    linarith
  by_cases hb0 : b ≤ 0
  · have : a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0 hb0
    linarith
  · push_neg at hb0
    have hab : a * b ≤ (1 + 2 * δ) * b := mul_le_mul_of_nonneg_right ha hb0.le
    have h2b : 2 * δ * b ≤ 2 * δ * M := mul_le_mul_of_nonneg_left hbM (by positivity)
    nlinarith

end RosserCostProvider
end ResearchBankV22
end Erdos287
