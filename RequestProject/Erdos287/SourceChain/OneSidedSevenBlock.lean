import RequestProject.Erdos287.CurrentTail.TailBoundary

/-!
# Erdős #287 — source chain: the one-sided seven-block moment consumer

**ERDŐS #287 REMAINS OPEN.  TAIL-287 IS NOT BANKED.**

The frozen `SevenBlockMainTermDictionary` asks for *two-sided* closeness of both normalised
moments to `(μ, ν)` with error controlled by `|R_Σ^P|/𝒩_X I` alone.  A physical Maynard-type
argument only supplies

* a **lower** bound for the first moment, `𝔼P ≥ μ_lo - e₁(X)`, and
* an **upper** bound for the pair moment, `𝔼Q ≤ ν_up + e₂(X) + |R_Σ^P(X)|/𝒩_X I`,

with model/Euler errors `e₁, e₂ → 0` that do **not** vanish when `R_Σ^P = 0`.

Kernel-proved here:

* `one_sided_moment_ineq` — for any `μ, ν, δ` with `1 + δ ≤ μ` and the strict margin
  `4ν + 4δ < (μ-δ)² - 2(μ-δ)`, the one-sided bounds force `2(𝔼P + 2𝔼Q) < (𝔼P)²`
  (monotonicity of `P ↦ P² - 2P` on `P ≥ 1`);
* `seven_block_oneSided_margin` — the frozen values `μ = 999999`, `ν = 1700001700000/7`
  satisfy that margin with `δ = 1`;
* `OneSidedSevenBlockDictionary` — the corrected, physically faithful interface;
* `oneSided_of_twoSided` — the old two-sided dictionary implies the new one (with
  `e₁ = |R|/NI`, `e₂ = 0`), so the new interface is a weaker requirement;
* `seven_block_three_occupied_oneSided` / `seven_block_contact_false_oneSided` — three occupied
  blocks, hence a contradiction with an exact #287 word through the trusted affine compiler;
* `OneSidedSevenBlockTailFramework` and `tail_of_remainder_littleO_oneSided` — the revised tail
  boundary: framework with errors `e₁, e₂ → 0` + `R_Σ^P = o(𝒩_X I)` ⟹ `Tail287Statement`.

The framework is still an input (its construction needs the physical Maynard weights); nothing
here constructs it.
-/

open scoped BigOperators
open Finset

namespace Erdos287.SourceChain

open Erdos287 Erdos287.PostV71V87 Erdos287.PostV87V90R Erdos287.CurrentTail

/-- **One-sided moment inequality** (generic constants). -/
theorem one_sided_moment_ineq {μ ν δ P Q : ℝ} (hμ : 1 + δ ≤ μ)
    (hmargin : 4 * ν + 4 * δ < (μ - δ) ^ 2 - 2 * (μ - δ))
    (hP : μ - δ ≤ P) (hQ : Q ≤ ν + δ) : 2 * (P + 2 * Q) < P ^ 2 := by
  have h1 : (μ - δ) ^ 2 - 2 * (μ - δ) ≤ P ^ 2 - 2 * P := by
    nlinarith [mul_nonneg (sub_nonneg.2 hP) (show 0 ≤ P + (μ - δ) - 2 by linarith)]
  nlinarith

/-- The frozen constants satisfy the one-sided margin with `δ = 1`. -/
theorem seven_block_oneSided_margin :
    4 * nu7 + 4 * 1 < (mu7 - 1) ^ 2 - 2 * (mu7 - 1) := by
  unfold mu7 nu7; norm_num

/-- **Corrected (one-sided) seven-block dictionary.** -/
structure OneSidedSevenBlockDictionary {ι : Type*} [Fintype ι] (F : FiniteWeights)
    (Y : ℕ → ι → ℕ) (e₁ e₂ R NI : ℝ) : Prop where
  NI_pos : 0 < NI
  first_lower : mu7 - e₁ ≤ F.E (fun t => (Pcount Y t : ℝ))
  pair_upper : F.E (fun t => (Qcount Y t : ℝ)) ≤ nu7 + e₂ + |R| / NI

/-- The old two-sided dictionary implies the one-sided one, with model errors
`e₁ = |R|/NI` and `e₂ = 0`. -/
theorem oneSided_of_twoSided {ι : Type*} [Fintype ι] {F : FiniteWeights} {Y : ℕ → ι → ℕ}
    {R NI : ℝ} (D : SevenBlockMainTermDictionary F Y R NI) :
    OneSidedSevenBlockDictionary F Y (|R| / NI) 0 R NI where
  NI_pos := D.NI_pos
  first_lower := by linarith [(abs_le.1 D.first).1]
  pair_upper := by linarith [(abs_le.1 D.second).2]

/-- **Three occupied blocks from the one-sided bounds.** -/
theorem seven_block_three_occupied_oneSided {ι : Type*} [Fintype ι] {F : FiniteWeights}
    {Y : ℕ → ι → ℕ} {e₁ e₂ R NI : ℝ} (D : OneSidedSevenBlockDictionary F Y e₁ e₂ R NI)
    (he₁ : e₁ ≤ 1) (he₂ : e₂ + |R| / NI ≤ 1) :
    ∃ t ∈ F.T, 0 < F.w t ∧ 3 ≤ Zcount Y t := by
  have hP : mu7 - 1 ≤ F.E (fun t => (Pcount Y t : ℝ)) := by linarith [D.first_lower]
  have hQ : F.E (fun t => (Qcount Y t : ℝ)) ≤ nu7 + 1 := by linarith [D.pair_upper]
  have h := one_sided_moment_ineq (by unfold mu7; norm_num) seven_block_oneSided_margin hP hQ
  exact exists_occupancy_of_moment F Y 2 (by push_cast; linarith)

/-- **One-sided contact consumer**: contradiction with an exact #287 word. -/
theorem seven_block_contact_false_oneSided (W : ExactWord) {K : ℕ}
    (C : AffineContactCompiler 7 2 K) {H : ℕ} (F : FiniteWeights) {e₁ e₂ R NI : ℝ}
    (D : OneSidedSevenBlockDictionary F (blockCount C) e₁ e₂ R NI)
    (he₁ : e₁ ≤ 1) (he₂ : e₂ + |R| / NI ≤ 1)
    (hctrl : ∀ t ∈ F.T, 0 < F.w t → WindowControl C W.a W.M H t) : False := by
  obtain ⟨t, ht, hw, hZ⟩ := seven_block_three_occupied_oneSided D he₁ he₂
  rw [Zcount_blockCount] at hZ
  exact occupancy_contact_false W C (by norm_num) (by norm_num) (hctrl t ht hw) hZ

variable {ι : Type*}

/-- **Revised seven-block tail framework** (structural input; one-sided moments with model
errors `e₁, e₂ → 0`). -/
structure OneSidedSevenBlockTailFramework (S : TailSourceFamily ι) : Prop where
  errors : ∃ e₁ e₂ : ℕ → ℝ, (∀ ε > 0, ∃ X0 : ℕ, ∀ X ≥ X0, e₁ X ≤ ε ∧ e₂ X ≤ ε) ∧
    ∀ X0 : ℕ, ∃ M0 : ℕ, ∀ W : ExactWord, 1 < W.a → M0 ≤ W.M →
      ∃ X ≥ X0, ∃ (K : ℕ) (C : AffineContactCompiler 7 2 K) (F : FiniteWeights) (H : ℕ),
        OneSidedSevenBlockDictionary F (blockCount C) (e₁ X) (e₂ X) ((S.T X).RSigmaP)
          (S.target X) ∧
        ∀ t ∈ F.T, 0 < F.w t → WindowControl C W.a W.M H t

/-- **Revised framework + `R_Σ^P = o(𝒩_X I)` ⟹ asymptotic tail.** -/
theorem tail_of_remainder_littleO_oneSided (S : TailSourceFamily ι)
    (Fw : OneSidedSevenBlockTailFramework S)
    (h : IsLittleOTarget (fun X => (S.T X).RSigmaP) S.target) : Tail287Statement := by
  obtain ⟨e₁, e₂, he, hscale⟩ := Fw.errors
  obtain ⟨X1, hX1⟩ := h (1 / 2) (by norm_num)
  obtain ⟨X2, hX2⟩ := he (1 / 2) (by norm_num)
  obtain ⟨M0, hM0⟩ := hscale (max X1 X2)
  refine ⟨M0, fun A hA => ?_⟩
  by_contra hlt
  push_neg at hlt
  set W := ofCounterexample hA
  have ha : 1 < W.a := ofCounterexample_one_lt_a hA
  have hM : M0 ≤ W.M := by rw [ofCounterexample_M]; exact hlt
  obtain ⟨X, hX, K, C, F, H, D, hctrl⟩ := hM0 W ha hM
  have hR : |(S.T X).RSigmaP| ≤ 1 / 2 * S.target X := by
    simpa using hX1 X ((le_max_left _ _).trans hX)
  obtain ⟨h1, h2⟩ := hX2 X ((le_max_right _ _).trans hX)
  have hq : |(S.T X).RSigmaP| / S.target X ≤ 1 / 2 := by
    rw [div_le_iff₀ D.NI_pos]; linarith
  exact seven_block_contact_false_oneSided W C F D (by linarith) (by linarith) hctrl

end Erdos287.SourceChain
