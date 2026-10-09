import Mathlib

/-!
# Erdős #287 — Research Bank V26 §4.5 (cont.): the boundary budget

INTERNAL #287 RESEARCH PROGRAMME ONLY.  **Erdős #287 is `OPEN` here and is not claimed.**

With `L = log x` and `h = L^{-B}` the provider bound `x √h L^C + x^{1/2} L^C` is at most
`2 x L^{-A}` once `B ≥ 2(C + A)` and `L^{C+A} ≤ x^{1/2}`.

**LEAN BANK** (exact real-exponent arithmetic):
* `sqrt_rpow_neg` — `√(L^{-B}) = L^{-B/2}`;
* `boundary_first_term` — `x √(L^{-B}) L^C ≤ x L^{-A}` for `B ≥ 2(C+A)`, `L ≥ 1`;
* `boundary_second_term` — `x^{1/2} L^C ≤ x L^{-A}` when `L^{C+A} ≤ x^{1/2}`;
* `boundary_budget` — the sum is `≤ 2 x L^{-A}`.
-/

namespace Erdos287
namespace ResearchBankV26
namespace BoundaryBudget

theorem sqrt_rpow_neg {L : ℝ} (hL : 0 ≤ L) (B : ℝ) : Real.sqrt (L ^ (-B)) = L ^ (-B / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL]
  ring_nf

theorem boundary_first_term {L x B C A : ℝ} (hL : 1 ≤ L) (hx : 0 ≤ x) (hB : 2 * (C + A) ≤ B) :
    x * Real.sqrt (L ^ (-B)) * L ^ C ≤ x * L ^ (-A) := by
  have hL0 : 0 < L := by linarith
  rw [sqrt_rpow_neg hL0.le, mul_assoc, ← Real.rpow_add hL0]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) hx

theorem boundary_second_term {L x C A : ℝ} (hL : 0 < L) (hx : 0 ≤ x)
    (hLx : L ^ (C + A) ≤ Real.sqrt x) : Real.sqrt x * L ^ C ≤ x * L ^ (-A) := by
  have e : L ^ C = L ^ (C + A) * L ^ (-A) := by rw [← Real.rpow_add hL]; ring_nf
  rw [e, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hL.le _)
  calc Real.sqrt x * L ^ (C + A) ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_left hLx (Real.sqrt_nonneg _)
    _ = x := Real.mul_self_sqrt hx

/-- **Boundary budget** (LEAN BANK). -/
theorem boundary_budget {L x B C A : ℝ} (hL : 1 ≤ L) (hx : 0 ≤ x) (hB : 2 * (C + A) ≤ B)
    (hLx : L ^ (C + A) ≤ Real.sqrt x) :
    x * Real.sqrt (L ^ (-B)) * L ^ C + Real.sqrt x * L ^ C ≤ 2 * (x * L ^ (-A)) := by
  have h1 := boundary_first_term hL hx hB
  have h2 := boundary_second_term (by linarith) hx hLx
  linarith

end BoundaryBudget
end ResearchBankV26
end Erdos287
