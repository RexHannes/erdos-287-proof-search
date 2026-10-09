import RequestProject.Erdos287.ResearchBankV17.CorrectedLogP

/-!
# Erdős #287 — Research Bank V17 §3: uniform functional thinning

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

The parameter family, for `0 < δ ≤ 1/40000`:

    L_δ = ⌈704 / (δ log 2)⌉,  K = 2^{L_δ},  P = 12 K,  b = log P,  a = b + 120.

Quantifier order (enforced by the statements): **choose δ → construct the fixed tuple → let
x → ∞.**  Nothing is claimed uniformly in `x` and `δ` simultaneously.

The transcendental / integration layer (the functional score and Bernstein-tail margins at each
tuple) is isolated in the smallest provider, `FunctionalThinningProvider`: a uniform positive
lower bound `m₀` for the two margin functions on `(0, 1/40000]`.  It is never constructed.

Kernel-proved:
* `Ldelta_spec` (LEAN BANK) — `704 ≤ L_δ δ log 2`;
* `b_ge` (LEAN BANK) — `δ b ≥ 704` where `b = log P = (L_δ + 2) log 2 + log 3`;
* `a_gt_b` (LEAN BANK) — `a = b + 120 > b`;
* `uniform_thinning_conditional` (LEAN CONDITIONAL) — for every `δ ∈ (0, 1/40000]` the fixed
  tuple satisfies the arithmetic constraints and has margins `≥ m₀ > 0`; and for every actual
  quantity converging (as `x → ∞`, at that fixed tuple) to the functional margin, the actual
  margin is eventually positive, with a threshold `x₀` depending on `δ`;
* `no_uniform_x0` (FINITE REGRESSION / countermodel) — eventual positivity for each fixed `δ`
  does NOT give one `x₀` uniform in `δ`: `1 − 1/(δ x)` is a countermodel.
-/

namespace Erdos287
namespace ResearchBankV17
namespace UniformThinning

/-- `L_δ = ⌈704/(δ log 2)⌉`. -/
noncomputable def Ldelta (δ : ℝ) : ℕ := ⌈704 / (δ * Real.log 2)⌉₊

/-- `b_δ = log P_δ = (L_δ + 2) log 2 + log 3` (corrected formula, `CorrectedLogP.log_twelve_pow`). -/
noncomputable def bdelta (δ : ℝ) : ℝ := Real.log ((12 * 2 ^ Ldelta δ : ℕ) : ℝ)

/-- `a_δ = b_δ + 120`. -/
noncomputable def adelta (δ : ℝ) : ℝ := bdelta δ + 120

theorem bdelta_eq (δ : ℝ) :
    bdelta δ = ((Ldelta δ : ℝ) + 2) * Real.log 2 + Real.log 3 :=
  CorrectedLogP.log_twelve_pow _

/-- **`704 ≤ L_δ δ log 2`.** -/
theorem Ldelta_spec {δ : ℝ} (hδ : 0 < δ) : 704 ≤ (Ldelta δ : ℝ) * δ * Real.log 2 := by
  have hl := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have h := Nat.le_ceil (704 / (δ * Real.log 2))
  have hpos : 0 < δ * Real.log 2 := mul_pos hδ hl
  rw [div_le_iff₀ hpos] at h
  unfold Ldelta; linarith

/-- **`δ b_δ ≥ 704`.** -/
theorem b_ge {δ : ℝ} (hδ : 0 < δ) : 704 ≤ δ * bdelta δ := by
  have h := Ldelta_spec hδ
  have hl := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have h3 := CorrectedLogP.one_lt_log_three
  rw [bdelta_eq]
  nlinarith

theorem a_gt_b (δ : ℝ) : bdelta δ < adelta δ := by unfold adelta; linarith

/-- **The smallest functional thinning provider** (never constructed): a uniform positive lower
bound for the functional score margin and the Bernstein-tail margin of the tuple built from `δ`. -/
structure FunctionalThinningProvider (scoreMargin tailMargin : ℝ → ℝ) (m₀ : ℝ) : Prop where
  m₀_pos : 0 < m₀
  score : ∀ δ, 0 < δ → δ ≤ 1 / 40000 → m₀ ≤ scoreMargin δ
  tail : ∀ δ, 0 < δ → δ ≤ 1 / 40000 → m₀ ≤ tailMargin δ

/-- **Uniform thinning (conditional), with the quantifier order δ → tuple → x.** -/
theorem uniform_thinning_conditional {scoreMargin tailMargin : ℝ → ℝ} {m₀ : ℝ}
    (hF : FunctionalThinningProvider scoreMargin tailMargin m₀) :
    ∀ δ, 0 < δ → δ ≤ 1 / 40000 →
      (704 ≤ (Ldelta δ : ℝ) * δ * Real.log 2 ∧ adelta δ = bdelta δ + 120 ∧
        m₀ ≤ scoreMargin δ ∧ m₀ ≤ tailMargin δ) ∧
      ∀ actual : ℝ → ℝ,
        (∀ η > 0, ∃ x₀ : ℝ, ∀ x ≥ x₀, |actual x - scoreMargin δ| ≤ η) →
          ∃ x₀ : ℝ, ∀ x ≥ x₀, 0 < actual x := by
  intro δ hδ hδ'
  refine ⟨⟨Ldelta_spec hδ, rfl, hF.score δ hδ hδ', hF.tail δ hδ hδ'⟩, fun actual hconv => ?_⟩
  obtain ⟨x₀, hx⟩ := hconv (m₀ / 2) (by linarith [hF.m₀_pos])
  refine ⟨x₀, fun x hx' => ?_⟩
  have h1 := (abs_le.1 (hx x hx')).1
  have h2 := hF.score δ hδ hδ'
  have := hF.m₀_pos
  linarith

/-- **Regression: no uniform `x₀`.**  For each fixed `δ > 0`, `1 − 1/(δ x)` is eventually
positive, but no single `x₀` works for all `δ ∈ (0, 1/40000]`. -/
theorem no_uniform_x0 :
    (∀ δ : ℝ, 0 < δ → ∃ x₀ : ℝ, ∀ x ≥ x₀, 0 < 1 - 1 / (δ * x)) ∧
      ¬ ∃ x₀ : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 40000 → ∀ x ≥ x₀, 0 < 1 - 1 / (δ * x) := by
  refine ⟨fun δ hδ => ⟨2 / δ, fun x hx => ?_⟩, fun ⟨x₀, h⟩ => ?_⟩
  · have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
    have hδx : 2 ≤ δ * x := by
      have := mul_le_mul_of_nonneg_left hx hδ.le
      rwa [mul_div_cancel₀ _ hδ.ne'] at this
    have : 1 / (δ * x) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hδx
    linarith
  · set x := max x₀ 1
    have hx1 : (1 : ℝ) ≤ x := le_max_right _ _
    have hx0 : (0 : ℝ) < x := by linarith
    have hδ : 0 < 1 / (40000 * x) := by positivity
    have hδ' : 1 / (40000 * x) ≤ 1 / 40000 := by
      apply one_div_le_one_div_of_le (by norm_num); nlinarith
    have := h (1 / (40000 * x)) hδ hδ' x (le_max_left _ _)
    have heq : 1 / (40000 * x) * x = 1 / 40000 := by field_simp
    rw [heq] at this
    norm_num at this

end UniformThinning
end ResearchBankV17
end Erdos287
