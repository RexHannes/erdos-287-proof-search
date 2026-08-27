import Mathlib

/-!
# Seven-prime `5|2` specialization — the deterministic exponent ledger

This file certifies the *rational exponent arithmetic* underlying the seven-prime
`5|2` specialization of a quadratic-Kummer bilinear bound.  No analytic input is used
or asserted: the content is exactly the inequality bookkeeping between the exponents.

## Ledger variables

With a scale parameter `Y > 1`, the specialization uses

* `M = Y^5`, `N = Y^2`, `X = Y^9`,
* `p = Y^θ` with `5/2 ≤ θ ≤ 8` (the two controlling endpoints being `θ = 5/2`
  and `θ = 8`).

The bilinear savings factor to be controlled is

`( Y^{-2} + p^{-1/2} + p^{1/2} Y^{-5} )^{1/2}`,

whose three exponents are `−2`, `−θ/2` and `θ/2 − 5`.

## Main results

* `exponent_ledger` — `max(−2, −θ/2, θ/2 − 5) ≤ −1` for all rational `θ ∈ [5/2, 8]`,
  and the two endpoint evaluations `exponent_ledger_endpoint_low` (`−5/4 ≤ −1`) and
  `exponent_ledger_endpoint_high` (`−1 ≤ −1`, the binding constraint);
* `kummer_savings_bound` — the real-analytic consequence
  `(Y^{-2} + p^{-1/2} + p^{1/2}Y^{-5})^{1/2} ≤ √3 · Y^{-1/2}` for `1 ≤ Y`;
* `margin_Y_eq_X` — the fixed-power margin `Y^{-1/2} = X^{-1/18}` for `X = Y^9`.

The `X^{o(1)}` factors of the source estimate are deliberately *not* modelled; only the
deterministic rational-exponent margin is certified here.
-/

open scoped BigOperators

namespace Erdos287
namespace KummerLedger

/-! ## The rational exponent ledger -/

/-- **Exponent ledger.**  For every rational `θ` with `5/2 ≤ θ ≤ 8`, all three exponents
occurring in the seven-prime `5|2` savings factor are at most `−1`. -/
theorem exponent_ledger (theta : ℚ) (h1 : 5/2 ≤ theta) (h2 : theta ≤ 8) :
    (-2 : ℚ) ≤ -1 ∧ -theta / 2 ≤ -1 ∧ theta / 2 - 5 ≤ -1 :=
  ⟨by norm_num, by linarith, by linarith⟩

/-- The same statement in `max` form. -/
theorem exponent_ledger_max (theta : ℚ) (h1 : 5/2 ≤ theta) (h2 : theta ≤ 8) :
    max (-2 : ℚ) (max (-theta / 2) (theta / 2 - 5)) ≤ -1 := by
  have h := exponent_ledger theta h1 h2
  simp only [max_le_iff]
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- Low endpoint `θ = 5/2` (`p = Y^{5/2}`): the controlling exponent is `−5/4 < −1`,
so there is slack. -/
theorem exponent_ledger_endpoint_low :
    max (-2 : ℚ) (max (-(5/2 : ℚ) / 2) ((5/2 : ℚ) / 2 - 5)) = -5/4 := by norm_num

/-- High endpoint `θ = 8` (`p = Y^8`): the controlling exponent is exactly `−1`, so the
ledger is tight and the margin is not lost. -/
theorem exponent_ledger_endpoint_high :
    max (-2 : ℚ) (max (-(8 : ℚ) / 2) ((8 : ℚ) / 2 - 5)) = -1 := by norm_num

/-- Beyond `θ = 8` the ledger fails: the third exponent exceeds `−1`.  This certifies
that the upper endpoint `p ≤ Y^8` is necessary, not decorative. -/
theorem exponent_ledger_fails_above_eight (theta : ℚ) (h : 8 < theta) :
    ¬ (theta / 2 - 5 ≤ -1) := by
  push_neg; linarith

/-! ## The real-analytic consequence -/

/-- Each of the three real terms is at most `Y^{-1}`. -/
theorem term_le (Y theta : ℝ) (hY : 1 ≤ Y) (h1 : 5/2 ≤ theta) (h2 : theta ≤ 8) :
    Y ^ (-2 : ℝ) ≤ Y ^ (-1 : ℝ) ∧
    (Y ^ theta) ^ (-(1 : ℝ)/2) ≤ Y ^ (-1 : ℝ) ∧
    (Y ^ theta) ^ ((1 : ℝ)/2) * Y ^ (-(5 : ℝ)) ≤ Y ^ (-1 : ℝ) := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  have e1 : (Y ^ theta) ^ (-(1 : ℝ)/2) = Y ^ (-theta/2) := by
    rw [← Real.rpow_mul hY0.le]
    congr 1
    ring
  have e2 : (Y ^ theta) ^ ((1 : ℝ)/2) * Y ^ (-(5 : ℝ)) = Y ^ (theta/2 - 5) := by
    rw [← Real.rpow_mul hY0.le, ← Real.rpow_add hY0]
    congr 1
    ring
  refine ⟨Real.rpow_le_rpow_of_exponent_le hY (by norm_num), ?_, ?_⟩
  · rw [e1]
    exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)
  · rw [e2]
    exact Real.rpow_le_rpow_of_exponent_le hY (by linarith)

/-- **Deterministic savings bound.**  For `1 ≤ Y` and `p = Y^θ` with `5/2 ≤ θ ≤ 8`,

`( Y^{-2} + p^{-1/2} + p^{1/2} Y^{-5} )^{1/2} ≤ √3 · Y^{-1/2}`. -/
theorem kummer_savings_bound (Y theta : ℝ) (hY : 1 ≤ Y) (h1 : 5/2 ≤ theta)
    (h2 : theta ≤ 8) :
    (Y ^ (-2 : ℝ) + (Y ^ theta) ^ (-(1 : ℝ)/2)
        + (Y ^ theta) ^ ((1 : ℝ)/2) * Y ^ (-(5 : ℝ))) ^ ((1 : ℝ)/2)
      ≤ Real.sqrt 3 * Y ^ (-(1 : ℝ)/2) := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  obtain ⟨t1, t2, t3⟩ := term_le Y theta hY h1 h2
  have hsum : Y ^ (-2 : ℝ) + (Y ^ theta) ^ (-(1 : ℝ)/2)
      + (Y ^ theta) ^ ((1 : ℝ)/2) * Y ^ (-(5 : ℝ)) ≤ 3 * Y ^ (-1 : ℝ) := by linarith
  have hnn : (0 : ℝ) ≤ Y ^ (-2 : ℝ) + (Y ^ theta) ^ (-(1 : ℝ)/2)
      + (Y ^ theta) ^ ((1 : ℝ)/2) * Y ^ (-(5 : ℝ)) := by positivity
  calc (Y ^ (-2 : ℝ) + (Y ^ theta) ^ (-(1 : ℝ)/2)
          + (Y ^ theta) ^ ((1 : ℝ)/2) * Y ^ (-(5 : ℝ))) ^ ((1 : ℝ)/2)
      ≤ (3 * Y ^ (-1 : ℝ)) ^ ((1 : ℝ)/2) :=
        Real.rpow_le_rpow hnn hsum (by norm_num)
    _ = Real.sqrt 3 * Y ^ (-(1 : ℝ)/2) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hY0.le,
          Real.sqrt_eq_rpow]
        norm_num

/-- **Fixed-power margin.**  With `X = Y^9` (`Y > 0`), the savings exponent `Y^{-1/2}`
is exactly `X^{-1/18}`. -/
theorem margin_Y_eq_X (Y : ℝ) (hY : 0 < Y) :
    Y ^ (-(1 : ℝ)/2) = (Y ^ (9 : ℝ)) ^ (-(1 : ℝ)/18) := by
  rw [← Real.rpow_mul hY.le]
  norm_num

/-- The margin in the ledger's own rational arithmetic: `9 · (−1/18) = −1/2`. -/
theorem margin_exponent : (9 : ℚ) * (-1/18) = -1/2 := by norm_num

end KummerLedger
end Erdos287
