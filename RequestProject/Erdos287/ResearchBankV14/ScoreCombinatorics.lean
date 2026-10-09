import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V14 §A7: score combinatorics

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For cell occupancies `P : Fin 11 → ℕ` the score is

    S = ∑_r [ P_r − (1/11) · binom(P_r, 2) ].

* `six_sub_cellScore` — for every natural `v`: `6 − (v − binom(v,2)/11) = (v−11)(v−12)/22`;
* `cellScore_le_six` — hence each cell contributes at most `6`;
* `score_le_18_of_three` — at most three occupied cells ⟹ `S ≤ 18`;
* `exists_gt_of_weighted_pos` — a **strictly positive** weighted average of `S(t) − 18` under
  **nonnegative** weights yields some `t` with `S(t) > 18` (and positive weight);
* `signed_weights_fail` — regression: with a signed weight the inference is false.
-/

namespace Erdos287
namespace ResearchBankV14
namespace ScoreCombinatorics

/-- The contribution `v − binom(v,2)/11` of a cell with `v` occupied points. -/
def cellScore (v : ℕ) : ℚ := v - (v.choose 2 : ℚ) / 11

/-- The score `S = ∑_r (P_r − binom(P_r,2)/11)`. -/
def score (P : Fin 11 → ℕ) : ℚ := ∑ r, cellScore (P r)

/-- **`6 − (v − binom(v,2)/11) = (v − 11)(v − 12)/22`.** -/
theorem six_sub_cellScore (v : ℕ) :
    6 - cellScore v = ((v : ℚ) - 11) * ((v : ℚ) - 12) / 22 := by
  unfold cellScore
  rw [Nat.cast_choose_two]
  ring

theorem sq_form_nonneg (v : ℕ) : 0 ≤ ((v : ℚ) - 11) * ((v : ℚ) - 12) / 22 := by
  apply div_nonneg _ (by norm_num)
  rcases le_or_gt v 11 with h | h
  · have : (v : ℚ) ≤ 11 := by exact_mod_cast h
    nlinarith
  · have : (12 : ℚ) ≤ v := by exact_mod_cast h
    nlinarith

theorem cellScore_le_six (v : ℕ) : cellScore v ≤ 6 := by
  have := six_sub_cellScore v
  have := sq_form_nonneg v
  linarith

theorem cellScore_zero : cellScore 0 = 0 := by simp [cellScore]

/-- The occupied cells. -/
def occupied (P : Fin 11 → ℕ) : Finset (Fin 11) := Finset.univ.filter fun r => P r ≠ 0

/-- **At most three occupied cells ⟹ `S ≤ 18`.** -/
theorem score_le_18_of_three (P : Fin 11 → ℕ) (h : (occupied P).card ≤ 3) : score P ≤ 18 := by
  unfold score
  have hsplit : ∑ r, cellScore (P r) = ∑ r ∈ occupied P, cellScore (P r) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r => P r ≠ 0)]
    have : ∑ r ∈ Finset.univ.filter (fun r => ¬ P r ≠ 0), cellScore (P r) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hr
      rw [hr, cellScore_zero]
    rw [this, add_zero]; rfl
  rw [hsplit]
  calc ∑ r ∈ occupied P, cellScore (P r) ≤ ∑ _r ∈ occupied P, (6 : ℚ) :=
        Finset.sum_le_sum fun r _ => cellScore_le_six _
    _ = 6 * (occupied P).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ 6 * 3 := by
        have : ((occupied P).card : ℚ) ≤ 3 := by exact_mod_cast h
        linarith
    _ = 18 := by norm_num

/-- Contrapositive: `S > 18` forces at least four occupied cells. -/
theorem four_occupied_of_score_gt (P : Fin 11 → ℕ) (h : 18 < score P) : 4 ≤ (occupied P).card := by
  by_contra h'
  push_neg at h'
  have := score_le_18_of_three P (by omega)
  linarith

/-- **Weighted averaging with nonnegative weights.** -/
theorem exists_gt_of_weighted_pos {ι : Type*} (s : Finset ι) (w g : ι → ℝ)
    (hw : ∀ t ∈ s, 0 ≤ w t) (hpos : 0 < ∑ t ∈ s, w t * (g t - 18)) :
    ∃ t ∈ s, 0 < w t ∧ 18 < g t := by
  by_contra h
  push_neg at h
  have : ∑ t ∈ s, w t * (g t - 18) ≤ 0 := by
    apply Finset.sum_nonpos
    intro t ht
    rcases (hw t ht).lt_or_eq with hlt | heq
    · have := h t ht hlt
      exact mul_nonpos_of_nonneg_of_nonpos hlt.le (by linarith)
    · rw [← heq, zero_mul]
  linarith

/-- **Regression: signed weights do not license the inference.** -/
theorem signed_weights_fail :
    ¬ ∀ (w g : Unit → ℝ), 0 < ∑ t ∈ (Finset.univ : Finset Unit), w t * (g t - 18) →
      ∃ t, 18 < g t := by
  intro h
  obtain ⟨t, ht⟩ := h (fun _ => -1) (fun _ => 17) (by norm_num)
  norm_num at ht

end ScoreCombinatorics
end ResearchBankV14
end Erdos287
