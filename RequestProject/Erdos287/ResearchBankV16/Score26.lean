import Mathlib.Tactic

/-!
# Erdős #287 — Research Bank V16 §2: the Route-C score function

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

For group occupancies `P : ZMod 26 → ℕ` the Route-C score is

    S = ∑_r f(P_r),   f(v) = v − (1/99) · binom(v, 2).

Kernel-proved (LEAN BANK):
* `fifty_sub_f` — `50 − f(v) = (v − 99)(v − 100)/198` in `ℚ`, for every natural `v`;
* `f_le_fifty` — hence each group contributes at most `50`;
* `score_le_350_of_seven` — at most seven occupied groups ⟹ `S ≤ 350`;
* `eight_occupied_of_score_gt` — `S > 350` ⟹ at least eight occupied groups;
* `exists_gt_of_weighted_pos` — a strictly positive weighted mean of `S(t) − 350` under
  **nonnegative** weights yields a point with `S(t) > 350` (nonnegativity is an explicit
  hypothesis);
* `signed_weights_fail` — regression: with a signed weight the inference is false.
-/

namespace Erdos287
namespace ResearchBankV16
namespace Score26

/-- `f(v) = v − binom(v,2)/99`. -/
def f (v : ℕ) : ℚ := v - (v.choose 2 : ℚ) / 99

/-- The Route-C score. -/
def score (P : ZMod 26 → ℕ) : ℚ := ∑ r, f (P r)

/-- **`50 − f(v) = (v − 99)(v − 100)/198`.** -/
theorem fifty_sub_f (v : ℕ) : 50 - f v = ((v : ℚ) - 99) * ((v : ℚ) - 100) / 198 := by
  unfold f; rw [Nat.cast_choose_two]; ring

theorem quad_nonneg (v : ℕ) : 0 ≤ ((v : ℚ) - 99) * ((v : ℚ) - 100) / 198 := by
  apply div_nonneg _ (by norm_num)
  rcases le_or_gt v 99 with h | h
  · have : (v : ℚ) ≤ 99 := by exact_mod_cast h
    nlinarith
  · have : (100 : ℚ) ≤ v := by exact_mod_cast h
    nlinarith

theorem f_le_fifty (v : ℕ) : f v ≤ 50 := by
  have := fifty_sub_f v; have := quad_nonneg v; linarith

/-- Equality cases: `f(99) = f(100) = 50`. -/
theorem f_99 : f 99 = 50 := by unfold f; norm_num [Nat.choose_two_right]
theorem f_100 : f 100 = 50 := by unfold f; norm_num [Nat.choose_two_right]

theorem f_zero : f 0 = 0 := by simp [f]

/-- Occupied groups. -/
def occupied (P : ZMod 26 → ℕ) : Finset (ZMod 26) := Finset.univ.filter fun r => P r ≠ 0

/-- **At most seven occupied groups ⟹ `S ≤ 350`.** -/
theorem score_le_350_of_seven (P : ZMod 26 → ℕ) (h : (occupied P).card ≤ 7) : score P ≤ 350 := by
  unfold score
  have hsplit : ∑ r, f (P r) = ∑ r ∈ occupied P, f (P r) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r => P r ≠ 0)]
    have : ∑ r ∈ Finset.univ.filter (fun r => ¬ P r ≠ 0), f (P r) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hr
      rw [hr, f_zero]
    rw [this, add_zero]; rfl
  rw [hsplit]
  calc ∑ r ∈ occupied P, f (P r) ≤ ∑ _r ∈ occupied P, (50 : ℚ) :=
        Finset.sum_le_sum fun r _ => f_le_fifty _
    _ = 50 * (occupied P).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ 50 * 7 := by
        have : ((occupied P).card : ℚ) ≤ 7 := by exact_mod_cast h
        linarith
    _ = 350 := by norm_num

/-- `S > 350` forces at least eight occupied groups. -/
theorem eight_occupied_of_score_gt (P : ZMod 26 → ℕ) (h : 350 < score P) :
    8 ≤ (occupied P).card := by
  by_contra h'
  push_neg at h'
  have := score_le_350_of_seven P (by omega)
  linarith

/-- **Weighted averaging with nonnegative weights** (threshold `350`). -/
theorem exists_gt_of_weighted_pos {ι : Type*} (s : Finset ι) (w g : ι → ℝ)
    (hw : ∀ t ∈ s, 0 ≤ w t) (hpos : 0 < ∑ t ∈ s, w t * (g t - 350)) :
    ∃ t ∈ s, 0 < w t ∧ 350 < g t := by
  by_contra h
  push_neg at h
  have : ∑ t ∈ s, w t * (g t - 350) ≤ 0 := by
    apply Finset.sum_nonpos
    intro t ht
    rcases (hw t ht).lt_or_eq with hlt | heq
    · have := h t ht hlt
      exact mul_nonpos_of_nonneg_of_nonpos hlt.le (by linarith)
    · rw [← heq, zero_mul]
  linarith

/-- **Regression: signed weights do not license the inference.** -/
theorem signed_weights_fail :
    ¬ ∀ (w g : Unit → ℝ), 0 < ∑ t ∈ (Finset.univ : Finset Unit), w t * (g t - 350) →
      ∃ t, 350 < g t := by
  intro h
  obtain ⟨t, ht⟩ := h (fun _ => -1) (fun _ => 349) (by norm_num)
  norm_num at ht

end Score26
end ResearchBankV16
end Erdos287
