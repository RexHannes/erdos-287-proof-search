import Mathlib

/-!
# V16, Part 5 — the exact Pascadi parameter no-go (rational ledger only)

This file formalises **one elementary rational implication and nothing else**:

if `η ≥ 0` and `3/5 ≤ 5/8 − 100 η`, then `η ≤ 1/4000`;

together with `1/7 > 1/4000`, hence no `η` can satisfy `η ≥ 1/7` and
`3/5 ≤ 5/8 − 100 η` simultaneously.

Classification: `PASCADI-Q3/5-Y1/7-PARAMETER-NOGO : PROVED_ALGEBRAIC / PARAMETER_LEDGER`.

**Honesty statement.**  Pascadi's analytic theorem is **not** formalised here, and nothing
in this file says that it fails, or that any published statement is false.  All that is
proved is arithmetic about the *parameters* `Q = X^{3/5}`, `y = X^{1/7}` in the shape
`3/5 ≤ 5/8 − 100 η`: the two requested parameter values are incompatible with that
inequality.  Whether that inequality is the correct rendering of any published hypothesis is
a **source** question, not a Lean one.  All arithmetic is exact over `ℚ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos287
namespace PascadiLedger

/-- **`pascadi_parameter_eta_le_one_div_4000`** — `PROVED_ALGEBRAIC / PARAMETER_LEDGER`.

If `η ≥ 0` and `3/5 ≤ 5/8 − 100 η`, then `η ≤ 1/4000`.  (The nonnegativity hypothesis was
requested explicitly; the implication in fact holds without it, since
`100 η ≤ 5/8 − 3/5 = 1/40`.) -/
theorem pascadi_parameter_eta_le_one_div_4000 (eta : ℚ) (h0 : 0 ≤ eta)
    (h : (3 : ℚ) / 5 ≤ 5 / 8 - 100 * eta) : eta ≤ 1 / 4000 := by
  have hnonneg : (0 : ℚ) ≤ eta := h0
  have hbudget : 100 * eta ≤ 1 / 40 := by linarith
  linarith [hnonneg, hbudget]

/-- **`one_div_seven_gt_one_div_4000`** — `1/7 > 1/4000`. -/
theorem one_div_seven_gt_one_div_4000 : (1 : ℚ) / 7 > 1 / 4000 := by norm_num

/-- **`pascadi_Q_three_fifths_y_one_seventh_incompatible`** —
`PROVED_ALGEBRAIC / PARAMETER_LEDGER`.

There is no `η` with `η ≥ 0`, `η ≥ 1/7` and `3/5 ≤ 5/8 − 100 η`. -/
theorem pascadi_Q_three_fifths_y_one_seventh_incompatible :
    ¬ ∃ eta : ℚ, 0 ≤ eta ∧ (1 : ℚ) / 7 ≤ eta ∧ (3 : ℚ) / 5 ≤ 5 / 8 - 100 * eta := by
  rintro ⟨eta, h0, h7, h⟩
  have hle : eta ≤ 1 / 4000 := pascadi_parameter_eta_le_one_div_4000 eta h0 h
  have := one_div_seven_gt_one_div_4000
  linarith

/-- The margin, exactly: at `η = 1/7` the inequality `3/5 ≤ 5/8 − 100 η` fails by
`5/8 − 100/7 − 3/5 = −(3993/280)`. -/
theorem pascadi_margin_at_one_seventh :
    (5 : ℚ) / 8 - 100 * (1 / 7) - 3 / 5 = -(3993 / 280) := by norm_num

end PascadiLedger
end Erdos287
